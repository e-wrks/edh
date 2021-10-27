module Language.Edh.Batteries.Console where

import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad (void)
import Data.Lossless.Decimal
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

      evalMsg !exit' = evalExprSrc rhExpr $
        \ !rhVal -> exit' $ edhDeCaseWrap rhVal

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
      (SrcLoc !doc (SrcRange !stmt'start _stmt'end)) = callingSrcLoc ctx

      evalMsg !exit' = exit' $ case args of
        [!val] | odNull kwargs -> val
        _ -> EdhArgsPack $ ArgsPack args kwargs

conOutputLog ::
  Text ->
  EdhValue ->
  ((EdhValue -> EdhTx) -> EdhTx) ->
  EdhTxExit EdhValue ->
  EdhTx
conOutputLog !logPos !levelVal !evalMsg !exit !ets =
  case parseSpec levelVal of
    Just !logLevel ->
      if logLevel < 0
        then do
          -- as the log queue is a TBQueue per se, log msgs from a failing STM
          -- transaction has no way to go into the queue then get logged, but
          -- the failing cases are especially in need of diagnostics, so
          -- negative log level number is used to instruct a debug trace.
          !th <- unsafeIOToSTM myThreadId
          let !tracePrefix =
                " 🐞 "
                  <> show th
                  <> " 👉 "
                  <> T.unpack logPos
                  <> " ❗ "
          runEdhTx ets $
            evalMsg $ \ !msgVal !ets' -> edhValueStr ets' msgVal $ \ !logStr ->
              trace (tracePrefix ++ T.unpack logStr) $
                exitEdh ets' exit nil
        else
          if logLevel < conLogLevel
            then -- drop log msg without even eval it
              exitEdh ets exit nil
            else runEdhTx ets $
              evalMsg $ \ !msgVal !ets' -> do
                let !srcLoc =
                      if conLogLevel <= 20
                        then -- with source location info
                          Just logPos
                        else -- no source location info
                          Nothing
                case msgVal of
                  EdhString !logStr -> do
                    logger logLevel srcLoc logStr
                    exitEdh ets' exit nil
                  !logVal -> edhValueJson ets' logVal $ \ !logJson -> do
                    logger logLevel srcLoc logJson
                    exitEdh ets' exit nil
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
  ArgsPack [v] !kwargs | odNull kwargs -> haltEdhProgram v ets
  _ -> haltEdhProgram (EdhArgsPack apk) ets

-- | The default Edh command prompts
-- ps1 is for single line, ps2 for multi-line
defaultEdhPS1, defaultEdhPS2 :: Text
defaultEdhPS1 = "Đ: "
defaultEdhPS2 = "Đ| "

-- | host method console.readSource(ps1="Đ: ", ps2="Đ| ")
conReadSourceProc ::
  "ps1" ?: Text -> "ps2" ?: Text -> "locInfo" ?: Bool -> EdhHostProc
conReadSourceProc
  (defaultArg defaultEdhPS1 -> !ps1)
  (defaultArg defaultEdhPS2 -> ps2)
  (defaultArg False -> locInfo)
  !exit
  !ets = do
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
    let doReadCmd :: Scope -> STM ()
        doReadCmd !cmdScope = do
          !cmdIn <- newEmptyTMVar
          runEdhTx ets $
            edhContIO $ do
              cio $ ConsoleIn cmdIn ps1 ps2
              atomically $
                readTMVar cmdIn
                  >>= \(EdhInput !name !lineNo !lines_) -> do
                    -- use a fresh dyamic effects cache
                    -- todo try reuse existing effects cache as possible?
                    !tipFrame <-
                      newCallFrame'
                        cmdScope
                        (edh'exe'src'loc tip)
                        (edh'exc'handler tip)
                    let !srcName = if T.null name then "<console>" else name
                        !etsCmd =
                          ets {edh'context = ctx {edh'ctx'tip = tipFrame}}
                    runEdhTx etsCmd $
                      evalEdh' srcName lineNo (T.unlines lines_) $
                        edhSwitchState ets . exitEdhTx exit
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
      tip = edh'ctx'tip ctx
      !world = edh'prog'world $ edh'thread'prog ets
      !cio = consoleIO $ edh'world'console world

-- | host method console.print(*args, **kwargs)
conPrintProc :: RestPosArgs -> RestKwArgs -> EdhHostProc
conPrintProc !args !kwargs !exit !ets =
  runEdhTx ets $ edhContIO $ printVS args $ odToList kwargs
  where
    !cio = consoleIO $ edh'world'console $ edh'prog'world $ edh'thread'prog ets

    printVS :: [EdhValue] -> [(AttrKey, EdhValue)] -> IO ()
    printVS [] [] = atomically $ exitEdh ets exit nil
    printVS [] ((k, v) : rest) = atomically $
      outStr v $ \ !s ->
        runEdhTx ets $
          edhContIO $ do
            cio $ ConsoleOut $ "  " <> attrKeyStr k <> "= " <> s <> "\n"
            printVS [] rest
    printVS (v : rest) !kvs = atomically $
      outStr v $ \ !s ->
        runEdhTx ets $
          edhContIO $ do
            cio $ ConsoleOut $ s <> "\n"
            printVS rest kvs

    outStr :: EdhValue -> (Text -> STM ()) -> STM ()
    outStr !v !exitRepr = case v of
      EdhString !s -> exitRepr s
      _ -> edhValueRepr ets v exitRepr

conNowProc :: EdhHostProc
conNowProc !exit !ets = do
  nanos <- (toNanoSecs <$>) $ unsafeIOToSTM $ getTime Realtime
  exitEdh ets exit (EdhDecimal $ fromInteger nanos)

timelyNotify ::
  EdhThreadState ->
  Integer ->
  Decimal ->
  Bool ->
  EdhTxExit EdhValue ->
  STM ()
timelyNotify !ets !scale !interval !wait1st !exit =
  case decimalToInteger interval of
    Nothing ->
      throwEdh ets UsageError $
        "invalid interval, expect an integer but: "
          <> T.pack (show interval)
    Just !i -> runEdhTx ets $
      edhContIO $ do
        let !delayMicros = scale * i
        -- use a 'TMVar' filled asynchronously, so perceivers on the same
        -- thread dont' get blocked by this wait
        !notif <- newEmptyTMVarIO
        !ns <- currNanos
        let schedNext last'ns = edhContIO $ do
              void $ -- avoid deadlock (thus process kill by RTS)
                forkFinally
                  ( do
                      !ns'now <- currNanos
                      threadDelay $
                        fromInteger $ max 0 $ delayMicros - (ns'now - last'ns)
                  )
                  ( const $ do
                      !curr'ns <- currNanos
                      atomically $ void $ tryPutTMVar notif curr'ns
                  )
              atomically notifOne
            notifOne = runEdhTx ets $
              edhContSTM $ do
                !last'ns <- takeTMVar notif
                runEdhTx ets $
                  edhYield
                    (EdhDecimal $ fromIntegral last'ns)
                    (const $ schedNext last'ns)
                    exit
        atomically $
          if wait1st
            then runEdhTx ets $ schedNext ns
            else do
              putTMVar notif ns
              notifOne
  where
    currNanos :: IO Integer
    currNanos = fromIntegral . toNanoSecs <$> getTime Realtime

-- | host generator console.everyMicros(n, wait1st=true) - with fixed interval
conEveryMicrosProc :: Decimal -> "wait1st" ?: Bool -> EdhHostProc
conEveryMicrosProc !interval (defaultArg True -> !wait1st) !exit !ets =
  timelyNotify ets 1 interval wait1st exit

-- | host generator console.everyMillis(n, wait1st=true) - with fixed interval
conEveryMillisProc :: Decimal -> "wait1st" ?: Bool -> EdhHostProc
conEveryMillisProc !interval (defaultArg True -> !wait1st) !exit !ets =
  timelyNotify ets 1000 interval wait1st exit

-- | host generator console.everySeconds(n, wait1st=true) - with fixed interval
conEverySecondsProc :: Decimal -> "wait1st" ?: Bool -> EdhHostProc
conEverySecondsProc !interval (defaultArg True -> !wait1st) !exit !ets =
  timelyNotify ets 1000000 interval wait1st exit
