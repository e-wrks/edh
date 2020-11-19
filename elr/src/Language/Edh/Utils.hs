module Language.Edh.Utils where

import           Prelude

import           Control.Concurrent.STM


seqcontSTM :: forall a . [(a -> STM ()) -> STM ()] -> ([a] -> STM ()) -> STM ()
seqcontSTM !xs !exit = go xs []
 where
  go :: [(a -> STM ()) -> STM ()] -> [a] -> STM ()
  go []         ys = exit $! reverse $! ys
  go (x : rest) ys = x $ \y -> go rest (y : ys)

foldcontSTM
  :: forall a
   . a
  -> (a -> a -> a)
  -> [(a -> STM ()) -> STM ()]
  -> (a -> STM ())
  -> STM ()
foldcontSTM !i !f !xs !exit = go i xs
 where
  go :: a -> [(a -> STM ()) -> STM ()] -> STM ()
  go !i' []         = exit $! i'
  go !i' (x : rest) = x $ \y -> go (f i' y) rest

mapcontSTM
  :: forall a b
   . (a -> b)
  -> [(a -> STM ()) -> STM ()]
  -> [(b -> STM ()) -> STM ()]
mapcontSTM !f !xs = go xs []
 where
  go
    :: [(a -> STM ()) -> STM ()]
    -> [(b -> STM ()) -> STM ()]
    -> [(b -> STM ()) -> STM ()]
  go []         ys = reverse $! ys
  go (x : rest) ys = go rest (y : ys) where y b = x (\a -> b (f a))

