
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
import           Data.Dynamic

import           Text.Megaparsec

import           Data.Lossless.Decimal          ( decimalToInteger )

import           Language.Edh.Control
import           Language.Edh.Runtime
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate
import           Language.Edh.Details.Utils


-- | operator (<|)
loggingProc :: EdhIntrinsicOp
loggingProc !lhExpr !rhExpr !exit !ets =
  runEdhTx ets $ evalExpr lhExpr $ \ !lhVal _ets ->
    case parseSpec $ edhDeCaseWrap lhVal of
      Just (logLevel, StmtSrc (srcPos, _)) -> if logLevel < 0
        -- as the log queue is a TBQueue per se, log msgs from a failing STM
        -- transaction has no way to go into the queue then get logged, but the
        -- failing cases are especially in need of diagnostics, so negative log
        -- level number is used to instruct a debug trace.
        then do
          !th <- unsafeIOToSTM myThreadId
          let !tracePrefix =
                " 🐞 " <> show th <> " 👉 " <> sourcePosPretty srcPos <> " ❗ "
          runEdhTx ets $ evalExpr rhExpr $ \ !rhVal _ets ->
            edhValueStr ets (edhDeCaseWrap rhVal) $ \ !logStr ->
              trace (tracePrefix ++ T.unpack logStr) $ exitEdh ets exit nil
        else if logLevel < conLogLevel
          then -- drop log msg without even eval it
               exitEdh ets exit nil
          else runEdhTx ets $ evalExpr rhExpr $ \ !rhVal _ets -> do
            let !rhv    = edhDeCaseWrap rhVal
                !srcLoc = if conLogLevel <= 20
                  then -- with source location info
                       Just $ sourcePosPretty srcPos
                  else -- no source location info
                       Nothing
            case rhv of
              EdhArgsPack !apk -> do
                logger logLevel srcLoc apk
                exitEdh ets exit nil
              _ -> do
                logger logLevel srcLoc $ ArgsPack [rhv] odEmpty
                exitEdh ets exit nil
      _ ->
        throwEdh ets EvalError $ "invalid log target: " <> T.pack (show lhVal)
 where
  !ctx         = edh'context ets
  !console     = edh'world'console $ edh'ctx'world ctx
  !conLogLevel = consoleLogLevel console
  !logger      = consoleLogger console

  parseSpec :: EdhValue -> Maybe (Int, StmtSrc)
  parseSpec = \case
    EdhDecimal !level ->
      (, edh'ctx'stmt ctx) . fromInteger <$> decimalToInteger level
    EdhPair (EdhDecimal !level) (EdhDecimal !unwind) ->
      liftA2 (,) (fromInteger <$> decimalToInteger level)
        $   edh'scope'caller
        .   contextFrame ctx
        .   fromInteger
        <$> decimalToInteger unwind
    _ -> Nothing


-- | host method console.exit(***apk)
--
-- this is currently equivalent to @throw ProgramHalt(***apk)@
conExitProc :: EdhHostProc
conExitProc !apk _ !ets = case apk of
  ArgsPack [v] !kwargs | odNull kwargs -> haltEdhProgram ets v
  _ -> haltEdhProgram ets $ EdhArgsPack apk


-- | The default Edh command prompts
-- ps1 is for single line, ps2 for multi-line
defaultEdhPS1, defaultEdhPS2 :: Text
defaultEdhPS1 = "Đ: "
defaultEdhPS2 = "Đ| "

-- | host method console.readSource(ps1="(db)Đ: ", ps2="(db)Đ| ")
conReadSourceProc :: EdhHostProc
conReadSourceProc !apk !exit !ets = if edh'in'tx ets
  then throwEdh ets
                UsageError
                "you don't read console from within a transaction"
  else case parseArgsPack (defaultEdhPS1, defaultEdhPS2) argsParser apk of
    Left  err        -> throwEdh ets UsageError err
    Right (ps1, ps2) -> do
      !cmdIn <- newEmptyTMVar
      writeTBQueue ioQ $ ConsoleIn cmdIn ps1 ps2
      runEdhTx ets
        $   edhContSTM
        $   readTMVar cmdIn
        >>= \(EdhInput !name !lineNo !lines_) -> case name of
              "" -> exitEdh ets exit $ EdhString $ T.unlines lines_
              _ ->
                exitEdh ets exit
                  $ EdhPair
                      (EdhPair (EdhString name)
                               (EdhDecimal $ fromIntegral lineNo)
                      )
                  $ EdhString
                  $ T.unlines lines_
 where
  !ctx = edh'context ets
  !ioQ = consoleIO $ edh'world'console $ edh'ctx'world ctx

  argsParser =
    ArgsPackParser
        [ \ !arg (_, ps2') -> case arg of
          EdhString ps1s -> Right (ps1s, ps2')
          _              -> Left "invalid ps1"
        , \ !arg (ps1', _) -> case arg of
          EdhString ps2s -> Right (ps1', ps2s)
          _              -> Left "invalid ps2"
        ]
      $ Map.fromList
          [ ( "ps1"
            , \ !arg (_, ps2') -> case arg of
              EdhString ps1s -> Right (ps1s, ps2')
              _              -> Left "invalid ps1"
            )
          , ( "ps2"
            , \ !arg (ps1', _) -> case arg of
              EdhString ps2s -> Right (ps1', ps2s)
              _              -> Left "invalid ps2"
            )
          ]

-- | host method console.readCommand(ps1="Đ: ", ps2="Đ| ", inScopeOf=None)
conReadCommandProc :: EdhHostProc
conReadCommandProc !apk !exit !ets = if edh'in'tx ets
  then throwEdh ets
                UsageError
                "you don't read console from within a transaction"
  else
    case parseArgsPack (defaultEdhPS1, defaultEdhPS2, Nothing) argsParser apk of
      Left err -> throwEdh ets UsageError err
      Right (ps1, ps2, inScopeOf) ->
        let
          doReadCmd :: Scope -> STM ()
          doReadCmd !cmdScope = do
            !cmdIn <- newEmptyTMVar
            writeTBQueue ioQ $ ConsoleIn cmdIn ps1 ps2
            runEdhTx ets
              $   edhContSTM
              $   readTMVar cmdIn
              >>= \(EdhInput !name !lineNo !lines_) ->
                    runEdhTx etsCmd
                      $ evalEdh'
                          (if T.null name then "<console>" else T.unpack name)
                          lineNo
                          (T.unlines lines_)
                      $ edhSwitchState ets
                      . exitEdhTx exit
           where
            !etsCmd = ets
              { edh'context = ctx
                { edh'ctx'stack =
                  cmdScope
                      {
                        -- mind to inherit caller's exception handler anyway
                        edh'excpt'hndlr  = edh'excpt'hndlr callerScope
                        -- use a meaningful caller stmt
                      , edh'scope'caller = StmtSrc
                                             ( SourcePos
                                               { sourceName   = "<console-cmd>"
                                               , sourceLine   = mkPos 1
                                               , sourceColumn = mkPos 1
                                               }
                                             , VoidStmt
                                             )
                      }
                    NE.:| NE.tail (edh'ctx'stack ctx)
                }
              }
        in
          case inScopeOf of
            Just !so -> case objectScope so of
              -- eval cmd source in scope of the specified object
              Just !inScope -> doReadCmd inScope
              Nothing       -> case edh'obj'store so of
                HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
                  -- the specified objec is a scope object, eval cmd source in
                  -- the wrapped scope
                  Just (inScope :: Scope) -> doReadCmd inScope
                  _                       -> throwEdh
                    ets
                    UsageError
                    "you don't read command inScopeOf a host object"
                _ -> error "bug: objectScope not working for non-host object"

            -- eval cmd source with caller's scope
            _ -> doReadCmd callerScope

 where
  !ctx         = edh'context ets
  !callerScope = contextFrame ctx 1
  !ioQ         = consoleIO $ edh'world'console $ edh'ctx'world ctx

  argsParser =
    ArgsPackParser
        [ \ !arg (_, ps2', so) -> case arg of
          EdhString ps1s -> Right (ps1s, ps2', so)
          _              -> Left "invalid ps1"
        , \ !arg (ps1', _, so) -> case arg of
          EdhString ps2s -> Right (ps1', ps2s, so)
          _              -> Left "invalid ps2"
        ]
      $ Map.fromList
          [ ( "ps1"
            , \ !arg (_, ps2', so) -> case arg of
              EdhString ps1s -> Right (ps1s, ps2', so)
              _              -> Left "invalid ps1"
            )
          , ( "ps2"
            , \ !arg (ps1', _, so) -> case arg of
              EdhString ps2s -> Right (ps1', ps2s, so)
              _              -> Left "invalid ps2"
            )
          , ( "inScopeOf"
            , \ !arg (ps1, ps2, _) -> case arg of
              EdhObject !so -> Right (ps1, ps2, Just so)
              _             -> Left "invalid inScopeOf object"
            )
          ]


-- | host method console.print(*args, **kwargs)
conPrintProc :: EdhHostProc
conPrintProc (ArgsPack !args !kwargs) !exit !ets = printVS args
  $ odToList kwargs
 where
  !ctx = edh'context ets
  !ioQ = consoleIO $ edh'world'console $ edh'ctx'world ctx

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
    _ -> edhValueRepr ets v $ \ !s -> do
      writeTBQueue ioQ
        $  ConsoleOut
        $  "  "
        <> T.pack (show k)
        <> "="
        <> s
        <> "\n"
      printVS [] rest
  printVS (v : rest) !kvs = case v of
    EdhString !s -> do
      writeTBQueue ioQ $ ConsoleOut $ s <> "\n"
      printVS rest kvs
    _ -> edhValueRepr ets v $ \ !s -> do
      writeTBQueue ioQ $ ConsoleOut $ s <> "\n"
      printVS rest kvs


conNowProc :: EdhHostProc
conNowProc _ !exit !ets = do
  nanos <- (toNanoSecs <$>) $ unsafeIOToSTM $ getTime Realtime
  exitEdh ets exit (EdhDecimal $ fromInteger nanos)


data PeriodicArgs = PeriodicArgs {
    periodic'interval :: !Int
  , periodic'wait1st :: !Bool
  }

timelyNotify
  :: EdhThreadState -> PeriodicArgs -> EdhGenrCaller -> EdhTxExit -> STM ()
timelyNotify !ets (PeriodicArgs !delayMicros !wait1st) !iter'cb !exit =
  if edh'in'tx ets
    then throwEdh ets UsageError "can not be called from within a transaction"
    else do -- use a 'TMVar' filled asynchronously, so perceivers on the same
      -- thread dont' get blocked by this wait
      !notif <- newEmptyTMVar
      let notifOne = do
            !nanos <- takeTMVar notif
            iter'cb (EdhDecimal $ fromInteger nanos) $ \case
              Left  !exv             -> edhThrow ets exv
              Right EdhBreak         -> exitEdh ets exit nil
              Right (EdhReturn !rtn) -> exitEdh ets exit rtn
              _                      -> schedNext
          schedNext = runEdhTx ets $ edhContIO $ do
            void $ forkIO $ do -- todo this is less optimal
              threadDelay delayMicros
              !nanos <- (toNanoSecs <$>) $ getTime Realtime
              atomically $ void $ tryPutTMVar notif nanos
            atomically $ edhDoSTM ets notifOne
      if wait1st
        then schedNext
        else do
          putTMVar notif =<< unsafeIOToSTM (toNanoSecs <$> getTime Realtime)
          notifOne


-- | host generator console.everyMicros(n, wait1st=true) - with fixed interval
conEveryMicrosProc :: EdhHostProc
conEveryMicrosProc !apk !exit !ets =
  case edh'ctx'genr'caller $ edh'context ets of
    Nothing -> throwEdh ets EvalError "can only be called as generator"
    Just genr'caller ->
      case parseArgsPack (PeriodicArgs 1 True) parsePeriodicArgs apk of
        Right !pargs -> timelyNotify ets pargs genr'caller exit
        Left  !err   -> throwEdh ets UsageError err

-- | host generator console.everyMillis(n, wait1st=true) - with fixed interval
conEveryMillisProc :: EdhHostProc
conEveryMillisProc !apk !exit !ets =
  case edh'ctx'genr'caller $ edh'context ets of
    Nothing -> throwEdh ets EvalError "can only be called as generator"
    Just genr'caller ->
      case parseArgsPack (PeriodicArgs 1 True) parsePeriodicArgs apk of
        Right !pargs -> timelyNotify
          ets
          pargs { periodic'interval = 1000 * periodic'interval pargs }
          genr'caller
          exit
        Left !err -> throwEdh ets UsageError err

-- | host generator console.everySeconds(n, wait1st=true) - with fixed interval
conEverySecondsProc :: EdhHostProc
conEverySecondsProc !apk !exit !ets =
  case edh'ctx'genr'caller $ edh'context ets of
    Nothing -> throwEdh ets EvalError "can only be called as generator"
    Just genr'caller ->
      case parseArgsPack (PeriodicArgs 1 True) parsePeriodicArgs apk of
        Right !pargs -> timelyNotify
          ets
          pargs { periodic'interval = 1000000 * periodic'interval pargs }
          genr'caller
          exit
        Left !err -> throwEdh ets UsageError err

parsePeriodicArgs :: ArgsPackParser PeriodicArgs
parsePeriodicArgs =
  ArgsPackParser
      [ \ !arg pargs -> case arg of
          EdhDecimal !d -> case decimalToInteger d of
            Just !i -> Right $ pargs { periodic'interval = fromIntegral i }
            _ -> Left $ "invalid interval, expect an integer but: " <> T.pack
              (show arg)
          _ -> Left $ "invalid interval, expect an integer but: " <> T.pack
            (show arg)
      ]
    $ Map.fromList
        [ ( "wait1st"
          , \ !arg pargs -> case arg of
            EdhBool !w -> Right pargs { periodic'wait1st = w }
            _ -> Left $ "invalid wait1st, expect true or false but: " <> T.pack
              (show arg)
          )
        ]

