{-# LANGUAGE
    GADTs
  , TypeApplications
#-}

module Language.Edh.Details.IOPD where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.ST

import           Control.Concurrent.STM

import           Data.Maybe
import           Data.Foldable
import           Data.Unique
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.ByteString                ( ByteString )
import qualified Data.ByteString               as B
import           Data.Hashable
import qualified Data.HashMap.Strict           as Map
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE
import           Data.Vector                    ( Vector )
import qualified Data.Vector                   as V
import qualified Data.Vector.Mutable           as MV
import           Data.Dynamic


-- | Mutable dict with insertion order preserved
-- (Insertion Order Preserving Dict)
--
-- An iopd can only be mutated through STM monad, conflicts wrt concurrent
-- modifications are resolved automatically by STM retry
data IOPD k v where
  IOPD ::(Eq k, Hashable k, Eq v, Hashable v) =>  {
      iopd'map :: {-# UNPACK #-} !(TVar (Map.HashMap k Int))
    , iopd'write'pos :: {-# UNPACK #-} !(TVar Int)
    , iopd'num'holes :: {-# UNPACK #-} !(TVar Int)
    , iopd'array :: {-# UNPACK #-} !(TVar (Vector (TVar (Maybe (k, v)))))
    } -> IOPD k v

iopdEmpty
  :: forall k v . (Eq k, Hashable k, Eq v, Hashable v) => STM (IOPD k v)
iopdEmpty = do
  mv  <- newTVar Map.empty
  wpv <- newTVar 0
  nhv <- newTVar 0
  av  <- newTVar V.empty
  return $ IOPD mv wpv nhv av

iopdNull
  :: forall k v . (Eq k, Hashable k, Eq v, Hashable v) => IOPD k v -> STM Bool
iopdNull (IOPD _mv !wpv !nhv _av) = do
  wp <- readTVar wpv
  nh <- readTVar nhv
  return (wp - nh <= 0)

iopdSize
  :: forall k v . (Eq k, Hashable k, Eq v, Hashable v) => IOPD k v -> STM Int
iopdSize (IOPD _mv !wpv !nhv _av) = do
  wp <- readTVar wpv
  nh <- readTVar nhv
  return $ wp - nh

iopdSingleton
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => k
  -> v
  -> STM (IOPD k v)
iopdSingleton !key !val = do
  mv  <- newTVar $ Map.singleton key 0
  wpv <- newTVar 1
  nhv <- newTVar 0
  av  <- newTVar . V.singleton =<< newTVar (Just (key, val))
  return $ IOPD mv wpv nhv av

iopdInsert
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => k
  -> v
  -> IOPD k v
  -> STM ()
iopdInsert !key !val (IOPD !mv !wpv _nhv !av) =
  Map.lookup key <$> readTVar mv >>= \case
    Just !i ->
      flip V.unsafeIndex i <$> readTVar av >>= flip writeTVar (Just (key, val))
    Nothing -> do
      entry <- newTVar $ Just (key, val)
      wp    <- readTVar wpv
      a     <- readTVar av
      let cap = V.length a
      if wp < cap
        then flip seq (modifyTVar' mv $ Map.insert key wp) $ runST $ do
          a' <- V.unsafeThaw a
          MV.unsafeWrite a' wp entry
        else do
          -- TODO find and fill holes under certain circumstances
          let !capNew = (cap +) $ max 7 $ quot cap 2
          let !aNew = runST $ do
                a' <- MV.unsafeNew capNew
                MV.unsafeCopy (MV.unsafeSlice 0 wp a')
                  =<< V.unsafeThaw (V.slice 0 wp a)
                MV.unsafeWrite a' wp entry
                V.unsafeFreeze a'
          writeTVar av aNew
      writeTVar wpv (wp + 1)

iopdLookup
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => k
  -> IOPD k v
  -> STM (Maybe v)
iopdLookup !key (IOPD !mv _wpv _nhv !av) =
  Map.lookup key <$> readTVar mv >>= \case
    Nothing -> return Nothing
    Just !i ->
      (fmap snd <$>) $ flip V.unsafeIndex i <$> readTVar av >>= readTVar

iopdLookupDefault
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => v
  -> k
  -> IOPD k v
  -> STM v
iopdLookupDefault !defaultVal !key !iopd = iopdLookup key iopd >>= \case
  Nothing   -> return defaultVal
  Just !val -> return val

iopdDelete
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => k
  -> IOPD k v
  -> STM ()
iopdDelete !key (IOPD !mv _wpv !nhv !av) =
  Map.lookup key <$> readTVar mv >>= \case
    Nothing -> return ()
    Just !i -> do
      flip V.unsafeIndex i <$> readTVar av >>= flip writeTVar Nothing
      modifyTVar' nhv (+ 1)

iopdKeys
  :: forall k v . (Eq k, Hashable k, Eq v, Hashable v) => IOPD k v -> STM [k]
iopdKeys (IOPD _mv !wpv _nhv !av) = do
  wp <- readTVar wpv
  a  <- readTVar av
  let go !keys !i | i < 0 = return keys
      go !keys !i         = readTVar (V.unsafeIndex a i) >>= \case
        Nothing           -> go keys (i - 1)
        Just (!key, _val) -> go (key : keys) (i - 1)
  go [] (wp - 1)

iopdToList
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => IOPD k v
  -> STM [(k, v)]
iopdToList (IOPD _mv !wpv _nhv !av) = do
  wp <- readTVar wpv
  a  <- readTVar av
  let go !entries !i | i < 0 = return entries
      go !entries !i         = readTVar (V.unsafeIndex a i) >>= \case
        Nothing     -> go entries (i - 1)
        Just !entry -> go (entry : entries) (i - 1)
  go [] (wp - 1)

iopdFromList
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => [(k, v)]
  -> STM (IOPD k v)
iopdFromList !entries = do
  tves <- sequence $ [ (key, ) <$> newTVar (Just e) | e@(!key, _) <- entries ]
  let (mNew, wpNew, nhNew, aNew) = runST $ do
        a <- MV.unsafeNew cap
        let go [] !m !wp !nh = (m, wp, nh, ) <$> V.unsafeFreeze a
            go ((!key, !ev) : rest) !m !wp !nh = case Map.lookup key m of
              Nothing -> do
                MV.unsafeWrite a wp ev
                go rest (Map.insert key wp m) (wp + 1) nh
              Just !i -> do
                MV.unsafeWrite a i ev
                go rest m wp nh
        go tves Map.empty 0 0
  mv  <- newTVar mNew
  wpv <- newTVar wpNew
  nhv <- newTVar nhNew
  av  <- newTVar aNew
  return $ IOPD mv wpv nhv av
  where cap = length entries



iopdSnapshot
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => IOPD k v
  -> STM (OrderedDict k v)
iopdSnapshot (IOPD !mv !wpv _nhv !av) = do
  m  <- readTVar mv
  wp <- readTVar wpv
  a  <- readTVar av
  a' <- V.sequence (readTVar <$> V.slice 0 wp a)
  return $ OrderedDict m a'


-- | Immutable dict with insertion order preserved
--
-- can be created either by 'odFromList', or taken as a snapshot of an IOPD
data OrderedDict k v where
  OrderedDict ::(Eq k, Hashable k, Eq v, Hashable v) => {
      od'map :: !(Map.HashMap k Int)
    , od'array :: !(Vector (Maybe (k, v)))
    } -> OrderedDict k v
instance (Eq k, Hashable k, Eq v, Hashable v) => Eq (OrderedDict k v) where
  x == y = odToList x == odToList y
instance (Eq k, Hashable k, Eq v, Hashable v) => Hashable (OrderedDict k v) where
  hashWithSalt s od@(OrderedDict m _a) =
    s `hashWithSalt` m `hashWithSalt` odToList od

odEmpty :: forall k v . (Eq k, Hashable k, Eq v, Hashable v) => OrderedDict k v
odEmpty = OrderedDict Map.empty V.empty

odNull
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => OrderedDict k v
  -> Bool
odNull (OrderedDict !m _a) = Map.null m

odTakeOut
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => k
  -> OrderedDict k v
  -> (Maybe v, OrderedDict k v)
odTakeOut !key od@(OrderedDict !m !a) = case Map.lookup key m of
  Nothing -> (Nothing, od)
  Just !i -> (snd <$> V.unsafeIndex a i, OrderedDict (Map.delete key m) a)

odToList
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => OrderedDict k v
  -> [(k, v)]
odToList (OrderedDict _m !a) = go [] (V.length a - 1)
 where
  go :: [(k, v)] -> Int -> [(k, v)]
  go entries !i | i < 0 = entries
  go entries !i         = case V.unsafeIndex a i of
    Nothing     -> go entries (i - 1)
    Just !entry -> go (entry : entries) (i - 1)

