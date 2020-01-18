{-# LANGUAGE  ScopedTypeVariables #-}

module Language.Edh.Details.Utils where

import           Prelude

import qualified Data.Map.Strict               as Map


-- TODO seek more optimal method for this
takeOutFromMap :: Ord k => k -> Map.Map k a -> (Maybe a, Map.Map k a)
takeOutFromMap k m = (p, Map.union left right)
  where (left, p, right) = Map.splitLookup k m


takeOutFromList :: forall a . (a -> Bool) -> [a] -> (Maybe a, [a])
takeOutFromList _ [] = (Nothing, [])
takeOutFromList p xs = go [] xs
 where
  go :: [a] -> [a] -> (Maybe a, [a])
  go leftOut [] = (Nothing, reverse leftOut)
  go leftOut (x : xs') =
    if p x then (Just x, reverse leftOut ++ xs') else go (x : leftOut) xs'

