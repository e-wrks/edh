{-# LANGUAGE  ScopedTypeVariables #-}

module Language.Edh.Details.Utils where

import           Prelude

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import           Data.Hashable
import qualified Data.HashMap.Strict           as Map

import           Language.Edh.Details.RtTypes


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


data ArgsPackParser a = ArgsPackParser {
    pos'parsers :: [EdhValue -> a -> Either Text a]
    , kw'parsers :: Map.HashMap AttrName (EdhValue ->  a -> Either Text a)
  }
parseArgsPack :: a -> ArgsPackParser a -> ArgsPack -> Either Text a
parseArgsPack defVal (ArgsPackParser posParsers kwParsers) (ArgsPack posArgs kwArgs)
  = go posParsers kwParsers posArgs (Map.toList kwArgs) defVal
 where
  go
    :: [EdhValue -> a -> Either Text a]
    -> Map.HashMap AttrName (EdhValue -> a -> Either Text a)
    -> [EdhValue]
    -> [(AttrName, EdhValue)]
    -> a
    -> Either Text a
  go _  _    []      []                     result = Right result
  go [] _    (_ : _) _                      _      = Left "too many args"
  go _  kwps []      ((kwn, kwv) : kwargs') result = case Map.lookup kwn kwps of
    Nothing  -> Left $ "unknown arg: " <> kwn
    Just kwp -> kwp kwv result >>= go [] kwps [] kwargs'
  go (p : posParsers') kwps (arg : args') kwargs result =
    p arg result >>= go posParsers' kwps args' kwargs


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

