
module Language.Edh.Batteries.Console where

import           Prelude
import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad.Reader
import           Control.Concurrent
import           Control.Concurrent.STM

import           System.Clock

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.List.NonEmpty            as NE
import qualified Data.HashMap.Strict           as Map

import           Text.Megaparsec

import           Data.Lossless.Decimal          ( castDecimalToInteger )

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | operator (<|)
loggingProc :: EdhIntrinsicOp
loggingProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  let !ctx                  = edh'context pgs
      (StmtSrc (srcPos, _)) = contextStmt ctx
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case lhVal of
    -- TODO interpret a pair of decimals at left-hand to be
    --        logging-level : stack-rewind-count
    --      and use source position at the stack frame after specified rewinding
    EdhDecimal d -> do
      let !logLevel = fromInteger $ castDecimalToInteger d
      -- as the log queue is a TQueue per se, log msgs from a failing STM
      -- transaction has no way to go into the queue then get logged, but the
      -- failing cases are especially in need of diagnostics, so negative log
      -- level number is used to instruct a debug trace.
      if logLevel < 0
        then
          let tracePrefix = " 🐞 " ++ sourcePosPretty srcPos ++ " ❗ "
          in
            evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case rhVal of
              EdhString !logStr ->
                trace (tracePrefix ++ T.unpack logStr) $ exitEdhProc exit nil
              _ -> edhValueRepr rhVal $ \(OriginalValue !rhRepr _ _) ->
                case rhRepr of
                  EdhString !logStr ->
                    trace (tracePrefix ++ T.unpack logStr)
                      $ exitEdhProc exit nil
                  _ ->
                    trace (tracePrefix ++ show rhRepr) $ exitEdhProc exit nil
        else contEdhSTM $ do
          let console      = worldConsole $ contextWorld ctx
              !conLogLevel = consoleLogLevel console
              !logger      = consoleLogger console
          if logLevel < conLogLevel
            then -- drop log msg without even eval it
                 exitEdhSTM pgs exit nil
            else
              runEdhProc pgs $ evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
                do
                  let !srcLoc = if conLogLevel <= 20
                        then -- with source location info
                             Just $ sourcePosPretty srcPos
                        else -- no source location info
                             Nothing
                  contEdhSTM $ case rhVal of
                    EdhArgsPack pkargs -> do
                      logger logLevel srcLoc pkargs
                      exitEdhSTM pgs exit nil
                    EdhTuple vals -> do
                      logger logLevel srcLoc $ ArgsPack vals Map.empty
                      exitEdhSTM pgs exit nil
                    _ -> do
                      logger logLevel srcLoc $ ArgsPack [rhVal] Map.empty
                      exitEdhSTM pgs exit nil
    _ -> throwEdh EvalError $ "Invalid log level: " <> T.pack (show lhVal)


-- | host method console.exit(***apk)
--
-- this just throws a 'ProgramHalt', godforbid no one recover from it.
conExitProc :: EdhProcedure
conExitProc !apk _ = ask >>= \pgs -> -- cross check with 'createEdhWorld'
  contEdhSTM $ _getEdhErrClass pgs (AttrByName "ProgramHalt") >>= \ec ->
    runEdhProc pgs $ createEdhObject ec apk $ \(OriginalValue !exv _ _) ->
      edhThrow exv


-- | The default Edh command prompts
-- ps1 is for single line, ps2 for multi-line
defaultEdhPS1, defaultEdhPS2 :: Text
defaultEdhPS1 = "Đ: "
defaultEdhPS2 = "Đ| "

-- | host method console.readCommand(ps1="(db)Đ: ", ps2="(db)Đ| ", inScopeOf=None)
conReadCommandProc :: EdhProcedure
conReadCommandProc !apk !exit = ask >>= \pgs ->
  case parseArgsPack (defaultEdhPS1, defaultEdhPS2, Nothing) argsParser apk of
    Left  err                   -> throwEdh UsageError err
    Right (ps1, ps2, inScopeOf) -> contEdhSTM $ do
      let !ioQ     = consoleIO $ worldConsole $ contextWorld $ edh'context pgs
          ctx      = edh'context pgs
          cmdScope = case inScopeOf of
            Just !so -> (contextScope ctx)
              -- eval cmd source in the specified object's (probably a module)
              -- context, while inherit this host proc's exception handler
              { scopeEntity = objEntity so
              , thisObject  = so
              , thatObject  = so
              , scopeProc   = objClass so
              , scopeCaller = StmtSrc
                                ( SourcePos { sourceName   = "<cmd-in>"
                                            , sourceLine   = mkPos 1
                                            , sourceColumn = mkPos 1
                                            }
                                , VoidStmt
                                )
              }
            _ -> case NE.tail $ callStack ctx of
              -- eval cmd source with caller's this/that, and lexical context,
              -- while the entity is already the same as caller's
              callerScope : _ -> (contextScope ctx)
                { thisObject  = thisObject callerScope
                , thatObject  = thatObject callerScope
                , scopeProc   = scopeProc callerScope
                , scopeCaller = scopeCaller callerScope
                }
              _ -> contextScope ctx
          !pgsCmd = pgs
            { edh'context = ctx
                              { callStack = cmdScope
                                              NE.:| NE.tail (callStack ctx)
                              }
            }
      cmdIn <- newEmptyTMVar
      writeTQueue ioQ $ ConsoleIn cmdIn ps1 ps2
      waitEdhSTM pgs (EdhString <$> readTMVar cmdIn) $ \case
        EdhString !cmdCode ->
          runEdhProc pgsCmd $ evalEdh "<console>" cmdCode exit
        _ -> error "impossible"
 where
  argsParser =
    ArgsPackParser
        [ \arg (_, ps2', so) -> case arg of
          EdhString ps1s -> Right (ps1s, ps2', so)
          _              -> Left "Invalid ps1"
        , \arg (ps1', _, so) -> case arg of
          EdhString ps2s -> Right (ps1', ps2s, so)
          _              -> Left "Invalid ps2"
        ]
      $ Map.fromList
          [ ( "ps1"
            , \arg (_, ps2', so) -> case arg of
              EdhString ps1s -> Right (ps1s, ps2', so)
              _              -> Left "Invalid ps1"
            )
          , ( "ps2"
            , \arg (ps1', _, so) -> case arg of
              EdhString ps2s -> Right (ps1', ps2s, so)
              _              -> Left "Invalid ps2"
            )
          , ( "inScopeOf"
            , \arg (ps1, ps2, _) -> case arg of
              EdhObject so -> Right (ps1, ps2, Just so)
              _            -> Left "Invalid inScopeOf object"
            )
          ]


-- | host method console.print(*args, **kwargs)
conPrintProc :: EdhProcedure
conPrintProc (ArgsPack !args !kwargs) !exit = ask >>= \pgs -> contEdhSTM $ do
  let !ioQ = consoleIO $ worldConsole $ contextWorld $ edh'context pgs
      printVS :: [EdhValue] -> [(AttrName, EdhValue)] -> STM ()
      printVS [] []              = exitEdhSTM pgs exit nil
      printVS [] ((k, v) : rest) = case v of
        EdhString !s -> do
          writeTQueue ioQ $ ConsoleOut $ k <> "=" <> s <> "\n"
          printVS [] rest
        _ -> runEdhProc pgs $ edhValueRepr v $ \(OriginalValue !vr _ _) ->
          case vr of
            EdhString !s -> contEdhSTM $ do
              writeTQueue ioQ $ ConsoleOut $ k <> "=" <> s <> "\n"
              printVS [] rest
            _ -> error "bug"
      printVS (v : rest) !kvs = case v of
        EdhString !s -> do
          writeTQueue ioQ $ ConsoleOut $ s <> "\n"
          printVS rest kvs
        _ -> runEdhProc pgs $ edhValueRepr v $ \(OriginalValue !vr _ _) ->
          case vr of
            EdhString !s -> contEdhSTM $ do
              writeTQueue ioQ $ ConsoleOut $ s <> "\n"
              printVS rest kvs
            _ -> error "bug"
  printVS args $ Map.toList kwargs


timelyNotify :: Int -> EdhGenrCaller -> STM ()
timelyNotify !delayMicros genr'caller@(!pgs', !iter'cb) = do
  nanos <- (toNanoSecs <$>) $ unsafeIOToSTM $ do
    threadDelay delayMicros
    getTime Realtime
  -- yield the nanosecond timestamp to iterator
  runEdhProc pgs' $ iter'cb (EdhDecimal $ fromInteger nanos) $ \_ ->
    timelyNotify delayMicros genr'caller

-- | host generator console.everyMicros(n) - with fixed interval
conEveryMicrosProc :: EdhProcedure
conEveryMicrosProc (ArgsPack !args !kwargs) _ = ask >>= \pgs ->
  case generatorCaller $ edh'context pgs of
    Nothing          -> throwEdh EvalError "Can only be called as generator"
    Just genr'caller -> case args of
      [EdhDecimal d] | Map.null kwargs ->
        let n = fromInteger $ castDecimalToInteger d
        in  contEdhSTM $ timelyNotify n genr'caller
      _ -> throwEdh EvalError "Invalid argument to console.everyMicros(n)"

-- | host generator console.everyMillis(n) - with fixed interval
conEveryMillisProc :: EdhProcedure
conEveryMillisProc (ArgsPack !args !kwargs) _ = ask >>= \pgs ->
  case generatorCaller $ edh'context pgs of
    Nothing          -> throwEdh EvalError "Can only be called as generator"
    Just genr'caller -> case args of
      [EdhDecimal d] | Map.null kwargs ->
        let n = 1000 * fromInteger (castDecimalToInteger d)
        in  contEdhSTM $ timelyNotify n genr'caller
      _ -> throwEdh EvalError "Invalid argument to console.everyMillis(n)"

-- | host generator console.everySeconds(n) - with fixed interval
conEverySecondsProc :: EdhProcedure
conEverySecondsProc (ArgsPack !args !kwargs) _ = ask >>= \pgs ->
  case generatorCaller $ edh'context pgs of
    Nothing          -> throwEdh EvalError "Can only be called as generator"
    Just genr'caller -> case args of
      [EdhDecimal d] | Map.null kwargs ->
        let n = 1000000 * fromInteger (castDecimalToInteger d)
        in  contEdhSTM $ timelyNotify n genr'caller
      _ -> throwEdh EvalError "Invalid argument to console.everySeconds(n)"

