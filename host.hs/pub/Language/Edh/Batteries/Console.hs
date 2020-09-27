
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
import           Data.Dynamic

import           Text.Megaparsec

import           Data.Lossless.Decimal          ( Decimal
                                                , decimalToInteger
                                                )

import           Language.Edh.Control
import           Language.Edh.Args
import           Language.Edh.Runtime
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


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
conExitProc :: ArgsPack -> EdhHostProc
conExitProc !apk _ !ets = case apk of
  ArgsPack [v] !kwargs | odNull kwargs -> haltEdhProgram ets v
  _ -> haltEdhProgram ets $ EdhArgsPack apk


-- | The default Edh command prompts
-- ps1 is for single line, ps2 for multi-line
defaultEdhPS1, defaultEdhPS2 :: Text
defaultEdhPS1 = "Đ: "
defaultEdhPS2 = "Đ| "

-- | host method console.readSource(ps1="(db)Đ: ", ps2="(db)Đ| ")
conReadSourceProc :: "ps1" ?: Text -> "ps2" ?: Text -> EdhHostProc
conReadSourceProc (defaultArg defaultEdhPS1 -> !ps1) (defaultArg defaultEdhPS2 -> ps2) !exit !ets
  = if edh'in'tx ets
    then throwEdh ets
                  UsageError
                  "you don't read console from within a transaction"
    else do
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

-- | host method console.readCommand(ps1="Đ: ", ps2="Đ| ", inScopeOf=None)
conReadCommandProc
  :: "ps1" ?: Text -> "ps2" ?: Text -> "inScopeOf" ?: Object -> EdhHostProc
conReadCommandProc (defaultArg defaultEdhPS1 -> !ps1) (defaultArg defaultEdhPS2 -> ps2) (optionalArg -> !inScopeOf) !exit !ets
  = if edh'in'tx ets
    then throwEdh ets
                  UsageError
                  "you don't read console from within a transaction"
    else
      let doReadCmd :: Scope -> STM ()
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
      in  case inScopeOf of
            Just !so -> castObjSelfStore so >>= \case
              -- the specified objec is a scope object, eval cmd source in
              -- the wrapped scope
              Just (inScope :: Scope) -> doReadCmd inScope
              -- eval cmd source in scope of the specified object
              Nothing -> objectScope so >>= \ !inScope -> doReadCmd inScope
            -- eval cmd source with caller's scope
            _ -> doReadCmd callerScope

 where
  !ctx         = edh'context ets
  !callerScope = contextFrame ctx 1
  !ioQ         = consoleIO $ edh'world'console $ edh'ctx'world ctx


-- | host method console.print(*args, **kwargs)
conPrintProc :: ArgsPack -> EdhHostProc
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
conNowProc !exit !ets = do
  nanos <- (toNanoSecs <$>) $ unsafeIOToSTM $ getTime Realtime
  exitEdh ets exit (EdhDecimal $ fromInteger nanos)


timelyNotify
  :: EdhThreadState
  -> Int
  -> Decimal
  -> Bool
  -> EdhGenrCaller
  -> EdhTxExit
  -> STM ()
timelyNotify !ets !scale !interval !wait1st !iter'cb !exit = if edh'in'tx ets
  then throwEdh ets UsageError "can not be called from within a transaction"
  else case decimalToInteger interval of
    Nothing ->
      throwEdh ets UsageError
        $  "invalid interval, expect an integer but: "
        <> T.pack (show interval)
    Just !i -> do
      let !delayMicros = scale * fromInteger i
      -- use a 'TMVar' filled asynchronously, so perceivers on the same
      -- thread dont' get blocked by this wait
      !notif <- newEmptyTMVar
      let notifOne = do
            !nanos <- takeTMVar notif
            iter'cb (EdhDecimal $ fromInteger nanos) $ \case
              Left (!etsThrower, !exv) ->
      -- note we can actually be encountering the exception occurred from
      -- a descendant thread forked by the thread running the enclosing
      -- generator, @etsThrower@ has the correct task queue, and @ets@
      -- has the correct contextual callstack anyway
                edhThrow etsThrower { edh'context = edh'context ets } exv
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
conEveryMicrosProc :: Decimal -> "wait1st" ?: Bool -> EdhHostProc
conEveryMicrosProc !interval (defaultArg True -> !wait1st) !exit !ets =
  case edh'ctx'genr'caller $ edh'context ets of
    Nothing          -> throwEdh ets EvalError "can only be called as generator"
    Just genr'caller -> timelyNotify ets 1 interval wait1st genr'caller exit

-- | host generator console.everyMillis(n, wait1st=true) - with fixed interval
conEveryMillisProc :: Decimal -> "wait1st" ?: Bool -> EdhHostProc
conEveryMillisProc !interval (defaultArg True -> !wait1st) !exit !ets =
  case edh'ctx'genr'caller $ edh'context ets of
    Nothing          -> throwEdh ets EvalError "can only be called as generator"
    Just genr'caller -> timelyNotify ets 1000 interval wait1st genr'caller exit

-- | host generator console.everySeconds(n, wait1st=true) - with fixed interval
conEverySecondsProc :: Decimal -> "wait1st" ?: Bool -> EdhHostProc
conEverySecondsProc !interval (defaultArg True -> !wait1st) !exit !ets =
  case edh'ctx'genr'caller $ edh'context ets of
    Nothing -> throwEdh ets EvalError "can only be called as generator"
    Just genr'caller ->
      timelyNotify ets 1000000 interval wait1st genr'caller exit

