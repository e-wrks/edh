
module Language.Edh.Batteries.Console where

import           Prelude
import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Applicative
import           Control.Monad.Reader
import           Control.Concurrent
import           Control.Concurrent.STM

import           System.Clock

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.List.NonEmpty            as NE
import qualified Data.HashMap.Strict           as Map

import           Text.Megaparsec

import           Data.Lossless.Decimal          ( decimalToInteger )

import           Language.Edh.Control
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate
import           Language.Edh.Details.Utils


-- | operator (<|)
loggingProc :: EdhIntrinsicOp
loggingProc !lhExpr !rhExpr !exit = do
  !ets <- ask
  let !ctx = edh'context ets
      parseSpec :: EdhValue -> Maybe (Int, StmtSrc)
      parseSpec = \case
        EdhDecimal !level ->
          (, contextStmt ctx) . fromInteger <$> decimalToInteger level
        EdhPair (EdhDecimal !level) (EdhDecimal !unwind) ->
          liftA2 (,) (fromInteger <$> decimalToInteger level)
            $   scopeCaller
            .   contextFrame ctx
            .   fromInteger
            <$> decimalToInteger unwind
        _ -> Nothing
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    case parseSpec $ edhDeCaseClose lhVal of
      Just (logLevel, StmtSrc (srcPos, _)) -> if logLevel < 0
        -- as the log queue is a TBQueue per se, log msgs from a failing STM
        -- transaction has no way to go into the queue then get logged, but the
        -- failing cases are especially in need of diagnostics, so negative log
        -- level number is used to instruct a debug trace.
        then contEdhSTM $ do
          th <- unsafeIOToSTM myThreadId
          let !tracePrefix =
                " 🐞 " <> show th <> " 👉 " <> sourcePosPretty srcPos <> " ❗ "
          runEdhTx ets $ evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
            case edhDeCaseClose rhVal of
              EdhString !logStr ->
                trace (tracePrefix ++ T.unpack logStr) $ exitEdhTx exit nil
              _ -> edhValueRepr rhVal $ \(OriginalValue !rhRepr _ _) ->
                case rhRepr of
                  EdhString !logStr ->
                    trace (tracePrefix ++ T.unpack logStr)
                      $ exitEdhTx exit nil
                  _ ->
                    trace (tracePrefix ++ show rhRepr) $ exitEdhTx exit nil
        else contEdhSTM $ do
          let console      = worldConsole $ contextWorld ctx
              !conLogLevel = consoleLogLevel console
              !logger      = consoleLogger console
          if logLevel < conLogLevel
            then -- drop log msg without even eval it
                 exitEdh ets exit nil
            else
              runEdhTx ets $ evalExpr rhExpr $ \(OriginalValue !rhV _ _) -> do
                let !rhVal  = edhDeCaseClose rhV
                    !srcLoc = if conLogLevel <= 20
                      then -- with source location info
                           Just $ sourcePosPretty srcPos
                      else -- no source location info
                           Nothing
                contEdhSTM $ case rhVal of
                  EdhArgsPack !apk -> do
                    logger logLevel srcLoc apk
                    exitEdh ets exit nil
                  _ -> do
                    logger logLevel srcLoc $ ArgsPack [rhVal] odEmpty
                    exitEdh ets exit nil
      _ -> throwEdh EvalError $ "invalid log target: " <> T.pack (show lhVal)


-- | host method console.exit(***apk)
--
-- this just throws a 'ProgramHalt', godforbid no one recover from it.
conExitProc :: EdhHostProc
conExitProc !apk _ = ask >>= \ets -> -- cross check with 'createEdhWorld'
  contEdhSTM $ _getEdhErrClass ets (AttrByName "ProgramHalt") >>= \ec ->
    runEdhTx ets $ createEdhObject ec apk $ \(OriginalValue !exv _ _) ->
      edhThrow exv


-- | The default Edh command prompts
-- ps1 is for single line, ps2 for multi-line
defaultEdhPS1, defaultEdhPS2 :: Text
defaultEdhPS1 = "Đ: "
defaultEdhPS2 = "Đ| "

-- | host method console.readSource(ps1="(db)Đ: ", ps2="(db)Đ| ")
conReadSourceProc :: EdhHostProc
conReadSourceProc !apk !exit = ask >>= \ets ->
  case parseArgsPack (defaultEdhPS1, defaultEdhPS2) argsParser apk of
    Left  err        -> throwEdh UsageError err
    Right (ps1, ps2) -> contEdhSTM $ do
      let !ioQ = consoleIO $ worldConsole $ contextWorld $ edh'context ets
      cmdIn <- newEmptyTMVar
      writeTBQueue ioQ $ ConsoleIn cmdIn ps1 ps2
      edhPerformSTM ets (readTMVar cmdIn)
        $ \(EdhInput !name !lineNo !lines_) -> case name of
            "" -> exitEdhTx exit $ EdhString $ T.unlines lines_
            _ ->
              exitEdhTx exit
                $ EdhPair
                    (EdhPair (EdhString name) (EdhDecimal $ fromIntegral lineNo)
                    )
                $ EdhString
                $ T.unlines lines_
 where
  argsParser =
    ArgsPackParser
        [ \arg (_, ps2') -> case arg of
          EdhString ps1s -> Right (ps1s, ps2')
          _              -> Left "invalid ps1"
        , \arg (ps1', _) -> case arg of
          EdhString ps2s -> Right (ps1', ps2s)
          _              -> Left "invalid ps2"
        ]
      $ Map.fromList
          [ ( "ps1"
            , \arg (_, ps2') -> case arg of
              EdhString ps1s -> Right (ps1s, ps2')
              _              -> Left "invalid ps1"
            )
          , ( "ps2"
            , \arg (ps1', _) -> case arg of
              EdhString ps2s -> Right (ps1', ps2s)
              _              -> Left "invalid ps2"
            )
          ]

-- | host method console.readCommand(ps1="Đ: ", ps2="Đ| ", inScopeOf=None)
conReadCommandProc :: EdhHostProc
conReadCommandProc !apk !exit = ask >>= \ets ->
  case parseArgsPack (defaultEdhPS1, defaultEdhPS2, Nothing) argsParser apk of
    Left  err                   -> throwEdh UsageError err
    Right (ps1, ps2, inScopeOf) -> contEdhSTM $ do
      let ctx  = edh'context ets
          !ioQ = consoleIO $ worldConsole $ contextWorld $ edh'context ets
      -- mind to inherit this host proc's exception handler anyway
      cmdScope <- case inScopeOf of
        Just !so -> isScopeWrapper ctx so >>= \case
          True -> return $ (wrappedScopeOf so)
            { exceptionHandler = exceptionHandler $ contextScope ctx
            }
          False -> return $ (contextScope ctx)
           -- eval cmd source in the specified object's (probably a module)
           -- context scope
            { scopeEntity = objEntity so
            , thisObject  = so
            , thatObject  = so
            , scopeProc   = objClass so
            , scopeCaller = StmtSrc
                              ( SourcePos { sourceName   = "<console-cmd>"
                                          , sourceLine   = mkPos 1
                                          , sourceColumn = mkPos 1
                                          }
                              , VoidStmt
                              )
            }
        _ -> case NE.tail $ callStack ctx of
          -- eval cmd source with caller's this/that, and lexical context,
          -- while the entity is already the same as caller's
          callerScope : _ -> return $ (contextScope ctx)
            { thisObject  = thisObject callerScope
            , thatObject  = thatObject callerScope
            , scopeProc   = scopeProc callerScope
            , scopeCaller = scopeCaller callerScope
            }
          _ -> return $ contextScope ctx
      let !etsCmd = ets
            { edh'context = ctx
                              { callStack        = cmdScope
                                                     NE.:| NE.tail (callStack ctx)
                              , contextExporting = False
                              }
            }
      cmdIn <- newEmptyTMVar
      writeTBQueue ioQ $ ConsoleIn cmdIn ps1 ps2
      edhPerformSTM ets (readTMVar cmdIn)
        $ \(EdhInput !name !lineNo !lines_) -> local (const etsCmd) $ evalEdh'
            (if T.null name then "<console>" else T.unpack name)
            lineNo
            (T.unlines lines_)
            exit
 where
  argsParser =
    ArgsPackParser
        [ \arg (_, ps2', so) -> case arg of
          EdhString ps1s -> Right (ps1s, ps2', so)
          _              -> Left "invalid ps1"
        , \arg (ps1', _, so) -> case arg of
          EdhString ps2s -> Right (ps1', ps2s, so)
          _              -> Left "invalid ps2"
        ]
      $ Map.fromList
          [ ( "ps1"
            , \arg (_, ps2', so) -> case arg of
              EdhString ps1s -> Right (ps1s, ps2', so)
              _              -> Left "invalid ps1"
            )
          , ( "ps2"
            , \arg (ps1', _, so) -> case arg of
              EdhString ps2s -> Right (ps1', ps2s, so)
              _              -> Left "invalid ps2"
            )
          , ( "inScopeOf"
            , \arg (ps1, ps2, _) -> case arg of
              EdhObject so -> Right (ps1, ps2, Just so)
              _            -> Left "invalid inScopeOf object"
            )
          ]


-- | host method console.print(*args, **kwargs)
conPrintProc :: EdhHostProc
conPrintProc (ArgsPack !args !kwargs) !exit = ask >>= \ets -> contEdhSTM $ do
  let !ioQ = consoleIO $ worldConsole $ contextWorld $ edh'context ets
      printVS :: [EdhValue] -> [(AttrKey, EdhValue)] -> STM ()
      printVS [] []              = exitEdh ets exit nil
      printVS [] ((k, v) : rest) = case v of
        EdhString !s -> do
          writeTBQueue ioQ
            $  ConsoleOut
            $  "  "
            <> T.pack (show k)
            <> "="
            <> s
            <> "\n"
          printVS [] rest
        _ -> runEdhTx ets $ edhValueRepr v $ \(OriginalValue !vr _ _) ->
          case vr of
            EdhString !s -> contEdhSTM $ do
              writeTBQueue ioQ
                $  ConsoleOut
                $  "  "
                <> T.pack (show k)
                <> "="
                <> s
                <> "\n"
              printVS [] rest
            _ -> error "bug"
      printVS (v : rest) !kvs = case v of
        EdhString !s -> do
          writeTBQueue ioQ $ ConsoleOut $ s <> "\n"
          printVS rest kvs
        _ -> runEdhTx ets $ edhValueRepr v $ \(OriginalValue !vr _ _) ->
          case vr of
            EdhString !s -> contEdhSTM $ do
              writeTBQueue ioQ $ ConsoleOut $ s <> "\n"
              printVS rest kvs
            _ -> error "bug"
  printVS args $ odToList kwargs


conNowProc :: EdhHostProc
conNowProc _ !exit = do
  ets <- ask
  contEdhSTM $ do
    nanos <- (toNanoSecs <$>) $ unsafeIOToSTM $ getTime Realtime
    exitEdh ets exit (EdhDecimal $ fromInteger nanos)


data PeriodicArgs = PeriodicArgs {
    periodic'interval :: !Int
  , periodic'wait1st :: !Bool
  }

timelyNotify
  :: EdhThreadState -> PeriodicArgs -> EdhGenrCaller -> EdhTxExit -> STM ()
timelyNotify !ets (PeriodicArgs !delayMicros !wait1st) (!ets', !iter'cb) !exit
  = if wait1st
    then edhPerformIO ets (threadDelay delayMicros) $ \() -> contEdhSTM notifOne
    else notifOne
 where
  notifOne = do
    nanos <- (toNanoSecs <$>) $ unsafeIOToSTM $ getTime Realtime
    runEdhTx ets' $ iter'cb (EdhDecimal $ fromInteger nanos) $ \case
      Left (etsThrower, exv) ->
        edhThrow etsThrower { edh'context = edh'context ets } exv
      Right EdhBreak         -> exitEdh ets exit nil
      Right (EdhReturn !rtn) -> exitEdh ets exit rtn
      _ ->
        edhPerformIO ets (threadDelay delayMicros) $ \() -> contEdhSTM notifOne

-- | host generator console.everyMicros(n, wait1st=true) - with fixed interval
conEveryMicrosProc :: EdhHostProc
conEveryMicrosProc !apk !exit = ask >>= \ets ->
  case generatorCaller $ edh'context ets of
    Nothing -> throwEdh EvalError "can only be called as generator"
    Just genr'caller ->
      case parseArgsPack (PeriodicArgs 1 True) parsePeriodicArgs apk of
        Right !pargs -> contEdhSTM $ timelyNotify ets pargs genr'caller exit
        Left  !err   -> throwEdh UsageError err

-- | host generator console.everyMillis(n, wait1st=true) - with fixed interval
conEveryMillisProc :: EdhHostProc
conEveryMillisProc !apk !exit = ask >>= \ets ->
  case generatorCaller $ edh'context ets of
    Nothing -> throwEdh EvalError "can only be called as generator"
    Just genr'caller ->
      case parseArgsPack (PeriodicArgs 1 True) parsePeriodicArgs apk of
        Right !pargs -> contEdhSTM $ timelyNotify
          ets
          pargs { periodic'interval = 1000 * periodic'interval pargs }
          genr'caller
          exit
        Left !err -> throwEdh UsageError err

-- | host generator console.everySeconds(n, wait1st=true) - with fixed interval
conEverySecondsProc :: EdhHostProc
conEverySecondsProc !apk !exit = ask >>= \ets ->
  case generatorCaller $ edh'context ets of
    Nothing -> throwEdh EvalError "can only be called as generator"
    Just genr'caller ->
      case parseArgsPack (PeriodicArgs 1 True) parsePeriodicArgs apk of
        Right !pargs -> contEdhSTM $ timelyNotify
          ets
          pargs { periodic'interval = 1000000 * periodic'interval pargs }
          genr'caller
          exit
        Left !err -> throwEdh UsageError err

parsePeriodicArgs :: ArgsPackParser PeriodicArgs
parsePeriodicArgs =
  ArgsPackParser
      [ \arg pargs -> case arg of
          EdhDecimal !d -> case decimalToInteger d of
            Just !i -> Right $ pargs { periodic'interval = fromIntegral i }
            _ -> Left $ "invalid interval, expect an integer but: " <> T.pack
              (show arg)
          _ -> Left $ "invalid interval, expect an integer but: " <> T.pack
            (show arg)
      ]
    $ Map.fromList
        [ ( "wait1st"
          , \arg pargs -> case arg of
            EdhBool !w -> Right pargs { periodic'wait1st = w }
            _ -> Left $ "invalid wait1st, expect true or false but: " <> T.pack
              (show arg)
          )
        ]

