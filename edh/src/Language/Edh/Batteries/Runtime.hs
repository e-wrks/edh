
module Language.Edh.Batteries.Runtime where

import           Prelude
import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad.Reader
import           Control.Concurrent
import           Control.Concurrent.STM

import           System.Clock

import qualified Data.Text                     as T
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
          let runtime     = worldRuntime $ contextWorld ctx
              !rtLogLevel = runtimeLogLevel runtime
              !logger     = runtimeLogger runtime
          if logLevel < rtLogLevel
            then -- drop log msg without even eval it
                 exitEdhSTM pgs exit nil
            else
              runEdhProc pgs $ evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
                do
                  let !srcLoc = if rtLogLevel <= 20
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


-- | host method runtime.exit(***apk)
rtExitProc :: EdhProcedure
rtExitProc _apk _ = ask >>= \pgs -> do
  -- TODO throw a `ProgramHalt` exception conveying the apk to program's halt result
  let !ioQ = consoleIO $ worldRuntime $ contextWorld $ edh'context pgs
  contEdhSTM $ writeTQueue ioQ ConsoleShutdown
  -- no CPS exit call, there's no return from `runtime.exit()`


-- | host method runtime.readCommands(ps1="(db)Đ: ", ps2="(db)Đ| ")
rtReadCommandsProc :: EdhProcedure
rtReadCommandsProc !apk _ = ask >>= \pgs ->
  case parseArgsPack ("Đ: ", "Đ| ") argsParser apk of
    Left  err        -> throwEdh EvalError err
    Right (ps1, ps2) -> case generatorCaller $ edh'context pgs of
      Nothing -> throwEdh EvalError "Can only be called as generator"
      Just (!pgs', !iter'cb) -> do
        let
          !ioQ = consoleIO $ worldRuntime $ contextWorld $ edh'context pgs
          readCmds :: STM ()
          readCmds = do
            cmdIn <- newEmptyTMVar
            writeTQueue ioQ $ ConsoleIn cmdIn ps1 ps2
            waitEdhSTM pgs (EdhString <$> readTMVar cmdIn) $ \case
              EdhString !cmdCode ->
                runEdhProc pgs' -- eval console code in for-loop's context
                  -- TODO don't let ParseError or other non-critical problem
                  --      crash the program, ultimantely after CPS exception
                  --      handling is implemented, we then enable Edh code to
                  --      catch exceptions and handle accordingly.
                  $ evalEdh "<console>" cmdCode
                  $ \(OriginalValue !cmdVal _ _) ->
                      contEdhSTM
                        $ runEdhProc pgs'
                        $ iter'cb
                            (EdhArgsPack $ ArgsPack [noneNil cmdVal] Map.empty)
                        $ const readCmds
              _ -> error "impossible"
        contEdhSTM readCmds
 where
  argsParser =
    ArgsPackParser
        [ \arg (_, ps2') -> case arg of
          EdhString ps1s -> Right (ps1s, ps2')
          _              -> Left "Invalid ps1"
        , \arg (ps1', _) -> case arg of
          EdhString ps2s -> Right (ps1', ps2s)
          _              -> Left "Invalid ps2"
        ]
      $ Map.fromList
          [ ( "ps1"
            , \arg (_, ps2') -> case arg of
              EdhString ps1s -> Right (ps1s, ps2')
              _              -> Left "Invalid ps1"
            )
          , ( "ps2"
            , \arg (ps1', _) -> case arg of
              EdhString ps2s -> Right (ps1', ps2s)
              _              -> Left "Invalid ps2"
            )
          ]


-- | host method runtime.print(*args, **kwargs)
rtPrintProc :: EdhProcedure
rtPrintProc (ArgsPack !args !kwargs) !exit = ask >>= \pgs -> contEdhSTM $ do
  let !ioQ = consoleIO $ worldRuntime $ contextWorld $ edh'context pgs
      printVS :: [EdhValue] -> [(AttrName, EdhValue)] -> STM ()
      printVS [] []              = exitEdhSTM pgs exit nil
      printVS [] ((k, v) : rest) = case v of
        EdhString !s -> do
          writeTQueue ioQ $ ConsoleOut $ k <> "=" <> s
          printVS [] rest
        _ -> runEdhProc pgs $ edhValueRepr v $ \(OriginalValue !vr _ _) ->
          case vr of
            EdhString !s -> contEdhSTM $ do
              writeTQueue ioQ $ ConsoleOut $ k <> "=" <> s
              printVS [] rest
            _ -> error "bug"
      printVS (v : rest) !kvs = case v of
        EdhString !s -> do
          writeTQueue ioQ $ ConsoleOut s
          printVS rest kvs
        _ -> runEdhProc pgs $ edhValueRepr v $ \(OriginalValue !vr _ _) ->
          case vr of
            EdhString !s -> contEdhSTM $ do
              writeTQueue ioQ $ ConsoleOut s
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

-- | host generator runtime.everyMicros(n) - with fixed interval
rtEveryMicrosProc :: EdhProcedure
rtEveryMicrosProc (ArgsPack !args !kwargs) _ = ask >>= \pgs ->
  case generatorCaller $ edh'context pgs of
    Nothing          -> throwEdh EvalError "Can only be called as generator"
    Just genr'caller -> case args of
      [EdhDecimal d] | Map.null kwargs ->
        let n = fromInteger $ castDecimalToInteger d
        in  contEdhSTM $ timelyNotify n genr'caller
      _ -> throwEdh EvalError "Invalid argument to runtime.everyMicros(n)"

-- | host generator runtime.everyMillis(n) - with fixed interval
rtEveryMillisProc :: EdhProcedure
rtEveryMillisProc (ArgsPack !args !kwargs) _ = ask >>= \pgs ->
  case generatorCaller $ edh'context pgs of
    Nothing          -> throwEdh EvalError "Can only be called as generator"
    Just genr'caller -> case args of
      [EdhDecimal d] | Map.null kwargs ->
        let n = 1000 * fromInteger (castDecimalToInteger d)
        in  contEdhSTM $ timelyNotify n genr'caller
      _ -> throwEdh EvalError "Invalid argument to runtime.everyMillis(n)"

-- | host generator runtime.everySeconds(n) - with fixed interval
rtEverySecondsProc :: EdhProcedure
rtEverySecondsProc (ArgsPack !args !kwargs) _ = ask >>= \pgs ->
  case generatorCaller $ edh'context pgs of
    Nothing          -> throwEdh EvalError "Can only be called as generator"
    Just genr'caller -> case args of
      [EdhDecimal d] | Map.null kwargs ->
        let n = 1000000 * fromInteger (castDecimalToInteger d)
        in  contEdhSTM $ timelyNotify n genr'caller
      _ -> throwEdh EvalError "Invalid argument to runtime.everySeconds(n)"

