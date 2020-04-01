{-# LANGUAGE  ScopedTypeVariables #-}

module Language.Edh.Details.Utils where

import           Prelude

import           Control.Concurrent.STM

import           Data.Hashable
import qualified Data.HashMap.Strict           as Map


-- TODO seek more optimal method for this
takeOutFromMap
  :: (Eq k, Hashable k) => k -> Map.HashMap k a -> (Maybe a, Map.HashMap k a)
takeOutFromMap k m = (Map.lookup k m, Map.delete k m)


takeOutFromList :: forall a . (a -> Bool) -> [a] -> (Maybe a, [a])
takeOutFromList _ [] = (Nothing, [])
takeOutFromList p xs = go [] xs
 where
  go :: [a] -> [a] -> (Maybe a, [a])
  go leftOut [] = (Nothing, reverse leftOut)
  go leftOut (x : xs') =
    if p x then (Just x, reverse leftOut ++ xs') else go (x : leftOut) xs'


seqcontSTM :: forall a . [(a -> STM ()) -> STM ()] -> ([a] -> STM ()) -> STM ()
seqcontSTM !xs !exit = go xs []
 where
  go :: [(a -> STM ()) -> STM ()] -> [a] -> STM ()
  go []         ys = exit $! reverse $! ys
  go (x : rest) ys = x $ \y -> go rest (y : ys)

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

