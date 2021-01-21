module Language.Edh.Utils where

import Control.Concurrent.STM (STM)
import Control.Monad
import System.Posix.Signals
import Prelude

seqcontSTM :: forall a. [(a -> STM ()) -> STM ()] -> ([a] -> STM ()) -> STM ()
seqcontSTM !xs !exit = go xs []
  where
    go :: [(a -> STM ()) -> STM ()] -> [a] -> STM ()
    go [] ys = exit $! reverse $! ys
    go (x : rest) ys = x $ \y -> go rest (y : ys)

foldcontSTM ::
  forall a.
  a ->
  (a -> a -> a) ->
  [(a -> STM ()) -> STM ()] ->
  (a -> STM ()) ->
  STM ()
foldcontSTM !i !f !xs !exit = go i xs
  where
    go :: a -> [(a -> STM ()) -> STM ()] -> STM ()
    go !i' [] = exit $! i'
    go !i' (x : rest) = x $ \y -> go (f i' y) rest

mapcontSTM ::
  forall a b.
  (a -> b) ->
  [(a -> STM ()) -> STM ()] ->
  [(b -> STM ()) -> STM ()]
mapcontSTM !f !xs = go xs []
  where
    go ::
      [(a -> STM ()) -> STM ()] ->
      [(b -> STM ()) -> STM ()] ->
      [(b -> STM ()) -> STM ()]
    go [] ys = reverse $! ys
    go (x : rest) ys = go rest (y : ys) where y b = x (b . f)

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
