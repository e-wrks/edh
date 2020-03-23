
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
              runEdhProg pgs $ evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
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


rtReadCommandsProc :: EdhProcedure
rtReadCommandsProc _ _ = ask >>= \pgs ->
  case generatorCaller $ edh'context pgs of
    Nothing -> throwEdh EvalError "Can only be called as generator"
    Just (!pgs', !iter'cb) -> do
      let !cioChan = consoleIO $ worldRuntime $ contextWorld $ edh'context pgs
          readCmds :: STM ()
          readCmds = do
            cmdIn <- newEmptyTMVar
            putTMVar cioChan $ Just cmdIn
            waitEdhSTM pgs (EdhString <$> readTMVar cmdIn) $ \case
              EdhString !cmdCode ->
                runEdhProg pgs' -- eval console code in caller's context
                  $ evalEdh "<console>" cmdCode
                  $ \(OriginalValue !cmdVal _ _) ->
                      contEdhSTM $ runEdhProg pgs' $ iter'cb cmdVal $ const
                        readCmds
              _ -> error "impossible"
      contEdhSTM readCmds


rtPrintProc :: EdhProcedure
rtPrintProc (ArgsPack !args !kwargs) !exit = ask >>= \pgs -> contEdhSTM $ do
  let !cioChan = consoleIO $ worldRuntime $ contextWorld $ edh'context pgs
      consoleOutput !txt = do
        co <- newTMVar txt
        putTMVar cioChan $ Just co
        return nil
      printVS :: [EdhValue] -> [(AttrName, EdhValue)] -> STM ()
      printVS [] []              = exitEdhSTM pgs exit nil
      printVS [] ((k, v) : rest) = case v of
        EdhString !s ->
          waitEdhSTM pgs (consoleOutput $ k <> "=" <> s) $ \_ -> printVS [] rest
        _ -> runEdhProg pgs $ edhValueRepr v $ \(OriginalValue !vr _ _) ->
          case vr of
            EdhString !s ->
              contEdhSTM
                $ waitEdhSTM pgs (consoleOutput $ k <> "=" <> s)
                $ \_ -> printVS [] rest
            _ -> error "bug"
      printVS (v : rest) !kvs = case v of
        EdhString !s ->
          waitEdhSTM pgs (consoleOutput s) $ \_ -> printVS rest kvs
        _ -> runEdhProg pgs $ edhValueRepr v $ \(OriginalValue !vr _ _) ->
          case vr of
            EdhString !s ->
              contEdhSTM $ waitEdhSTM pgs (consoleOutput s) $ \_ ->
                printVS rest kvs
            _ -> error "bug"
  printVS args $ Map.toList kwargs


timelyNotify :: Int -> EdhGenrCaller -> STM ()
timelyNotify !delayMicros genr'caller@(!pgs', !iter'cb) = do
  nanos <- (toNanoSecs <$>) $ unsafeIOToSTM $ do
    threadDelay delayMicros
    getTime Realtime
  -- yield the nanosecond timestamp to iterator
  runEdhProg pgs' $ iter'cb (EdhDecimal $ fromInteger nanos) $ \_ ->
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

