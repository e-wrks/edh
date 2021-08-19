module Language.Edh.Utils where

import Control.Concurrent.STM (STM)
import Control.Monad
import System.Posix.Signals
import Prelude

seqcontSTM :: forall a. [(a -> STM ()) -> STM ()] -> ([a] -> STM ()) -> STM ()
seqcontSTM !xs !exit = go xs []
  where
    go :: [(a -> STM ()) -> STM ()] -> [a] -> STM ()
    go [] ys = exit $! reverse ys
    go (x : rest) ys = x $ \y -> go rest (y : ys)

-- | Add a new signal handler, with the previous handler (if installed) kept
-- effective as well
--
-- CAVEAT
--  * this will disable default behavior if previously mandated
--  * this will destroy the ignore set of previous handler if installed with
addSignalHandler :: Signal -> IO () -> IO ()
addSignalHandler !s !h =
  installHandler s Default Nothing >>= \case
    Default -> noChain
    Ignore -> noChain
    Catch !h' -> installIt $
      Catch $ do
        h'
        h
    CatchOnce !h' -> installIt $
      CatchOnce $ do
        h'
        h
        void $ addSignalHandler s h
    CatchInfo !h' -> installIt $
      CatchInfo $ \si -> do
        h' si
        h
    CatchInfoOnce !h' -> installIt $
      CatchInfoOnce $ \si -> do
        h' si
        h
        addSignalHandler s h
  where
    noChain = installIt $ Catch h
    installIt h' = void $ installHandler s h' Nothing
