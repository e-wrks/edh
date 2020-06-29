{-# LANGUAGE  ScopedTypeVariables #-}

module Language.Edh.Details.Utils where

import           Prelude

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
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
    -> [(AttrKey, EdhValue)]
    -> a
    -> Either Text a
  go _  _    []      []                    result = Right result
  go [] _    (_ : _) _                     _      = Left "too many args"
  go _  kwps []      ((kw, kwv) : kwargs') result = case kw of
    AttrByName !kwn -> case Map.lookup kwn kwps of
      Nothing  -> Left $ "unknown arg: " <> kwn
      Just kwp -> kwp kwv result >>= go [] kwps [] kwargs'
    _ -> Left $ "unknown symbolic arg: " <> T.pack (show kw)
  go (p : posParsers') kwps (arg : args') kwargs result =
    p arg result >>= go posParsers' kwps args' kwargs


seqcontSTM :: forall a . [(a -> STM ()) -> STM ()] -> ([a] -> STM ()) -> STM ()
seqcontSTM !xs !exit = go xs []
 where
  go :: [(a -> STM ()) -> STM ()] -> [a] -> STM ()
  go []         ys = exit $! reverse $! ys
  go (x : rest) ys = x $ \y -> go rest (y : ys)

foldl'contSTM
  :: forall a
   . a
  -> (a -> a -> a)
  -> [(a -> STM ()) -> STM ()]
  -> (a -> STM ())
  -> STM ()
foldl'contSTM !i !f !xs !exit = go i xs
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

