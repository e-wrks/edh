module Language.Edh.Batteries.Console where

import Control.Concurrent (forkIO, myThreadId, threadDelay)
import Control.Concurrent.STM
import Control.Monad (void)
import Data.Lossless.Decimal
  ( Decimal,
    decimalToInteger,
  )
import Data.Text (Text)
import qualified Data.Text as T
import Debug.Trace (trace)
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Args
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.RtTypes
import Language.Edh.Runtime
import System.Clock (Clock (Realtime), getTime, toNanoSecs)
import Prelude

-- | operator (<|)
loggingProc :: EdhIntrinsicOp
loggingProc
  !lhExpr
  rhExpr@(ExprSrc _rhe (SrcRange !msg'start _msg'end))
  !exit
  !ets = runEdhTx ets $
    evalExprSrc lhExpr $ \ !lhVal ->
      conOutputLog
        (prettySrcPos doc msg'start)
        (edhDeCaseWrap lhVal)
        evalMsg
        exit
    where
      !ctx = edh'context ets
      (SrcLoc !doc _) = contextSrcLoc ctx

      evalMsg !exit' = runEdhTx ets $
        evalExprSrc rhExpr $
          \ !rhVal _ets -> exit' $ edhDeCaseWrap rhVal

-- | host method console.log(*args, level= console.info, **kwargs)
conLogProc :: RestPosArgs -> "level" ?: EdhValue -> RestPackArgs -> EdhHostProc
conLogProc
  !args
  (defaultArg (EdhDecimal 20) -> !levelVal)
  (ArgsPack _ !kwargs)
  !exit
  !ets =
    runEdhTx ets $
      conOutputLog
        (prettySrcPos doc stmt'start)
        levelVal
        evalMsg
        exit
    where
      !ctx = edh'context ets
      (SrcLoc !doc (SrcRange !stmt'start _stmt'end)) = contextSrcLoc ctx

      evalMsg !exit' = exit' $ case args of
        [!val] | odNull kwargs -> val
        _ -> EdhArgsPack $ ArgsPack args kwargs

conOutputLog :: Text -> EdhValue -> ((EdhValue -> STM ()) -> STM ()) -> EdhTxExit EdhValue -> EdhTx
conOutputLog !logPos !levelVal !evalMsg !exit !ets =
  case parseSpec levelVal of
    Just !logLevel ->
      if logLevel < 0
        then -- as the log queue is a TBQueue per se, log msgs from a failing STM
        -- transaction has no way to go into the queue then get logged, but the
        -- failing cases are especially in need of diagnostics, so negative log
        -- level number is used to instruct a debug trace.
        do
          !th <- unsafeIOToSTM myThreadId
          let !tracePrefix =
                " 🐞 "
                  <> show th
                  <> " 👉 "
                  <> T.unpack logPos
                  <> " ❗ "
          evalMsg $ \ !msgVal -> edhValueStr ets msgVal $ \ !logStr ->
            trace (tracePrefix ++ T.unpack logStr) $
              exitEdh ets exit nil
        else
          if logLevel < conLogLevel
            then -- drop log msg without even eval it
              exitEdh ets exit nil
            else evalMsg $ \ !msgVal -> do
              let !srcLoc =
                    if conLogLevel <= 20
                      then -- with source location info
                        Just logPos
                      else -- no source location info
                        Nothing
              case msgVal of
                EdhString !logStr -> do
                  logger logLevel srcLoc logStr
                  exitEdh ets exit nil
                !logVal -> edhValueJson ets logVal $ \ !logJson -> do
                  logger logLevel srcLoc logJson
                  exitEdh ets exit nil
    _ ->
      throwEdh ets EvalError $
        "invalid log target: " <> T.pack (show levelVal)
  where
    !console = edh'world'console $ edh'prog'world $ edh'thread'prog ets
    !conLogLevel = consoleLogLevel console
    !logger = consoleLogger console

    parseSpec :: EdhValue -> Maybe Int
    parseSpec = \case
      EdhDecimal !level -> fromInteger <$> decimalToInteger level
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
conReadSourceProc ::
  "ps1" ?: Text -> "ps2" ?: Text -> "locInfo" ?: Bool -> EdhHostProc
conReadSourceProc
  (defaultArg defaultEdhPS1 -> !ps1)
  (defaultArg defaultEdhPS2 -> ps2)
  (defaultArg False -> locInfo)
  !exit
  !ets =
    if edh'in'tx ets
      then
        throwEdh
          ets
          UsageError
          "you don't read console from within a transaction"
      else do
        !cmdIn <- newEmptyTMVar
        runEdhTx ets $
          edhContIO $ do
            cio $ ConsoleIn cmdIn ps1 ps2
            atomically $
              readTMVar cmdIn >>= \(EdhInput !name !lineNo !lines_) ->
                if locInfo
                  then
                    exitEdh ets exit $
                      EdhPair
                        ( EdhPair
                            (EdhString name)
                            (EdhDecimal $ fromIntegral lineNo)
                        )
                        $ EdhString $
                          T.unlines lines_
                  else exitEdh ets exit $ EdhString $ T.unlines lines_
    where
      !world = edh'prog'world $ edh'thread'prog ets
      !cio = consoleIO $ edh'world'console world

-- | host method console.readCommand(ps1="Đ: ", ps2="Đ| ", inScopeOf=None)
conReadCommandProc ::
  "ps1" ?: Text -> "ps2" ?: Text -> "inScopeOf" ?: Object -> EdhHostProc
conReadCommandProc
  (defaultArg defaultEdhPS1 -> !ps1)
  (defaultArg defaultEdhPS2 -> ps2)
  (optionalArg -> !inScopeOf)
  !exit
  !ets =
    if edh'in'tx ets
      then
        throwEdh
          ets
          UsageError
          "you don't read console from within a transaction"
      else
        let doReadCmd :: Scope -> STM ()
            doReadCmd !cmdScope = do
              !cmdIn <- newEmptyTMVar
              runEdhTx ets $
                edhContIO $ do
                  cio $ ConsoleIn cmdIn ps1 ps2
                  atomically $
                    readTMVar cmdIn
                      >>= \(EdhInput !name !lineNo !lines_) ->
                        let !srcName = if T.null name then "<console>" else name
                            !etsCmd =
                              ets
                                { edh'context =
                                    ctx
                                      { edh'ctx'tip =
                                          (edh'ctx'tip ctx)
                                            { edh'frame'scope = cmdScope
                                            }
                                      }
                                }
                         in runEdhTx etsCmd $
                              evalEdh' srcName lineNo (T.unlines lines_) $
                                edhSwitchState ets
                                  . exitEdhTx exit
         in case inScopeOf of
              Just !so ->
                castObjSelfStore so >>= \case
                  -- the specified objec is a scope object, eval cmd source in
                  -- the wrapped scope
                  Just (inScope :: Scope) -> doReadCmd inScope
                  -- eval cmd source in scope of the specified object
                  Nothing -> objectScope so >>= \ !inScope -> doReadCmd inScope
              -- eval cmd source with caller's scope
              _ -> doReadCmd (callingScope ctx)
    where
      !ctx = edh'context ets
      !world = edh'prog'world $ edh'thread'prog ets
      !cio = consoleIO $ edh'world'console world

-- | host method console.print(*args, eol= '\n', **kwargs)
conPrintProc :: RestPosArgs -> "eol" ?: Text -> RestPackArgs -> EdhHostProc
conPrintProc !args (defaultArg "\n" -> !eol) (ArgsPack _ !kwargs) !exit !ets =
  if edh'in'tx ets
    then
      throwEdh
        ets
        UsageError
        "you don't print to console from within a transaction"
    else runEdhTx ets $ edhContIO $ printVS args $ odToList kwargs
  where
    !cio = consoleIO $ edh'world'console $ edh'prog'world $ edh'thread'prog ets

    printVS :: [EdhValue] -> [(AttrKey, EdhValue)] -> IO ()
    printVS [] [] = atomically $ exitEdh ets exit nil
    printVS [] ((k, v) : rest) = case v of
      EdhString !s -> do
        cio $ ConsoleOut $ "  " <> attrKeyStr k <> "= " <> s <> eol
        printVS [] rest
      _ -> atomically $
        edhValueRepr ets v $ \ !s -> runEdhTx ets $
          edhContIO $ do
            cio $ ConsoleOut $ "  " <> attrKeyStr k <> "= " <> s <> eol
            printVS [] rest
    printVS (v : rest) !kvs = case v of
      EdhString !s -> do
        cio $ ConsoleOut $ s <> eol
        printVS rest kvs
      _ -> atomically $
        edhValueRepr ets v $ \ !s -> runEdhTx ets $
          edhContIO $ do
            cio $ ConsoleOut $ s <> eol
            printVS rest kvs

conNowProc :: EdhHostProc
conNowProc !exit !ets = do
  nanos <- (toNanoSecs <$>) $ unsafeIOToSTM $ getTime Realtime
  exitEdh ets exit (EdhDecimal $ fromInteger nanos)

timelyNotify ::
  EdhThreadState ->
  Int ->
  Decimal ->
  Bool ->
  EdhGenrCaller ->
  EdhTxExit EdhValue ->
  STM ()
timelyNotify !ets !scale !interval !wait1st !iter'cb !exit =
  if edh'in'tx ets
    then throwEdh ets UsageError "can not be called from within a transaction"
    else case decimalToInteger interval of
      Nothing ->
        throwEdh ets UsageError $
          "invalid interval, expect an integer but: "
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
                  -- note we can actually be encountering the exception occurred
                  -- from a descendant thread forked by the thread running the
                  -- enclosing generator, @etsThrower@ has the correct task
                  -- queue, and @ets@ has the correct contextual callstack
                  -- anyway
                  edhThrow etsThrower {edh'context = edh'context ets} exv
                Right EdhBreak -> exitEdh ets exit nil
                Right (EdhReturn !rtn) -> exitEdh ets exit rtn
                _ -> schedNext
            schedNext = runEdhTx ets $
              edhContIO $ do
                void $
                  forkIO $ do
                    -- todo this is less optimal
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
    Nothing -> throwEdh ets EvalError "can only be called as generator"
    Just genr'caller -> timelyNotify ets 1 interval wait1st genr'caller exit

-- | host generator console.everyMillis(n, wait1st=true) - with fixed interval
conEveryMillisProc :: Decimal -> "wait1st" ?: Bool -> EdhHostProc
conEveryMillisProc !interval (defaultArg True -> !wait1st) !exit !ets =
  case edh'ctx'genr'caller $ edh'context ets of
    Nothing -> throwEdh ets EvalError "can only be called as generator"
    Just genr'caller -> timelyNotify ets 1000 interval wait1st genr'caller exit

-- | host generator console.everySeconds(n, wait1st=true) - with fixed interval
conEverySecondsProc :: Decimal -> "wait1st" ?: Bool -> EdhHostProc
conEverySecondsProc !interval (defaultArg True -> !wait1st) !exit !ets =
  case edh'ctx'genr'caller $ edh'context ets of
    Nothing -> throwEdh ets EvalError "can only be called as generator"
    Just genr'caller ->
      timelyNotify ets 1000000 interval wait1st genr'caller exit
