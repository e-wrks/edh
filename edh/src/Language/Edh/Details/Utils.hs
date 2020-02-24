{-# LANGUAGE  ScopedTypeVariables #-}

module Language.Edh.Details.Utils where

import           Prelude

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

