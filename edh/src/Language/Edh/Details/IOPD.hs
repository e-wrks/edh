
module Language.Edh.Details.IOPD where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.ST

import           Control.Concurrent.STM

import           Data.Hashable
import qualified Data.HashMap.Strict           as Map
import           Data.Vector                    ( Vector )
import qualified Data.Vector                   as V
import qualified Data.Vector.Mutable           as MV


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
iopdInsert !key !val d@(IOPD !mv !wpv _nhv !av) =
  Map.lookup key <$> readTVar mv >>= \case
    Just !i ->
      flip V.unsafeIndex i <$> readTVar av >>= flip writeTVar (Just (key, val))
    Nothing -> do
      entry <- newTVar $ Just (key, val)
      wp0   <- readTVar wpv
      a0    <- readTVar av
      if wp0 >= V.length a0 then iopdReserve 7 d else pure ()
      wp <- readTVar wpv
      a  <- readTVar av
      if wp >= V.length a
        then error "bug: iopd reservation malfunctioned"
        else pure ()
      flip seq (modifyTVar' mv $ Map.insert key wp) $ runST $ do
        a' <- V.unsafeThaw a
        MV.unsafeWrite a' wp entry
      writeTVar wpv (wp + 1)

iopdReserve
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => Int
  -> IOPD k v
  -> STM ()
iopdReserve !moreCap (IOPD _mv !wpv _nhv !av) = do
  wp <- readTVar wpv
  a  <- readTVar av
  let !needCap = wp + moreCap
      !cap     = V.length a
  if cap >= needCap
    then return ()
    else do
      let !aNew = runST $ do
            a' <- MV.unsafeNew needCap
            MV.unsafeCopy (MV.unsafeSlice 0 wp a')
              =<< V.unsafeThaw (V.slice 0 wp a)
            V.unsafeFreeze a'
      writeTVar av aNew

iopdUpdate
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => [(k, v)]
  -> IOPD k v
  -> STM ()
iopdUpdate !ps !d = if null ps
  then return ()
  else do
    iopdReserve (length ps) d
    upd ps
 where
  upd []                    = return ()
  upd ((!key, !val) : rest) = do
    iopdInsert key val d
    upd rest

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

iopdToReverseList
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => IOPD k v
  -> STM [(k, v)]
iopdToReverseList (IOPD _mv !wpv _nhv !av) = do
  wp <- readTVar wpv
  a  <- readTVar av
  let go !entries !i | i >= wp = return entries
      go !entries !i           = readTVar (V.unsafeIndex a i) >>= \case
        Nothing     -> go entries (i + 1)
        Just !entry -> go (entry : entries) (i + 1)
  go [] 0

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

odLookup
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => k
  -> OrderedDict k v
  -> Maybe v
odLookup !key (OrderedDict !m !a) = case Map.lookup key m of
  Nothing -> Nothing
  Just !i -> snd <$> V.unsafeIndex a i

odLookupDefault
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => v
  -> k
  -> OrderedDict k v
  -> v
odLookupDefault !defaultVal !key !d = case odLookup key d of
  Nothing   -> defaultVal
  Just !val -> val

odTakeOut
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => k
  -> OrderedDict k v
  -> (Maybe v, OrderedDict k v)
odTakeOut !key od@(OrderedDict !m !a) = case Map.lookup key m of
  Nothing -> (Nothing, od)
  Just !i -> (snd <$> V.unsafeIndex a i, OrderedDict (Map.delete key m) a)

odKeys
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => OrderedDict k v
  -> [k]
odKeys (OrderedDict !m _a) = Map.keys m

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

odToReverseList
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => OrderedDict k v
  -> [(k, v)]
odToReverseList (OrderedDict _m !a) = go [] 0
 where
  !cap = V.length a
  go :: [(k, v)] -> Int -> [(k, v)]
  go entries !i | i >= cap = entries
  go entries !i            = case V.unsafeIndex a i of
    Nothing     -> go entries (i + 1)
    Just !entry -> go (entry : entries) (i + 1)

odFromList
  :: forall k v
   . (Eq k, Hashable k, Eq v, Hashable v)
  => [(k, v)]
  -> OrderedDict k v
odFromList !entries =
  let (mNew, aNew) = runST $ do
        a <- MV.unsafeNew $ length entries
        let go []                    !m _wp = (m, ) <$> V.unsafeFreeze a
            go (ev@(!key, _) : rest) !m !wp = case Map.lookup key m of
              Nothing -> do
                MV.unsafeWrite a wp $ Just ev
                go rest (Map.insert key wp m) (wp + 1)
              Just !i -> do
                MV.unsafeWrite a i $ Just ev
                go rest m wp
        go entries Map.empty 0
  in  OrderedDict mNew aNew

odMap
  :: forall k v v'
   . (Eq k, Hashable k, Eq v, Hashable v, Eq v', Hashable v')
  => (v -> v')
  -> OrderedDict k v
  -> OrderedDict k v'
odMap _f (OrderedDict !m _a) | Map.null m = OrderedDict Map.empty V.empty
odMap !f (OrderedDict !m !a) =
  let !aNew = runST $ do
        a' <- MV.unsafeNew $ V.length a
        MV.set a' Nothing
        let go []                  = V.unsafeFreeze a'
            go ((!key, !i) : rest) = do
              case V.unsafeIndex a i of
                Just (_, !val) -> MV.unsafeWrite a' i $ Just (key, f val)
                Nothing        -> pure () -- should fail hard in this case?
              go rest
        go (Map.toList m)
  in  OrderedDict m aNew

odMapSTM
  :: forall k v v'
   . (Eq k, Hashable k, Eq v, Hashable v, Eq v', Hashable v')
  => (v -> STM v')
  -> OrderedDict k v
  -> STM (OrderedDict k v')
odMapSTM _f (OrderedDict !m _a) | Map.null m =
  return $ OrderedDict Map.empty V.empty
odMapSTM !f (OrderedDict !m !a) =
  let !aNew = runST $ do
        a' <- MV.unsafeNew $ V.length a
        MV.set a' $ return Nothing
        let go []                  = V.unsafeFreeze a'
            go ((!key, !i) : rest) = do
              case V.unsafeIndex a i of
                Just (_, !val) ->
                  MV.unsafeWrite a' i $ Just . (key, ) <$> f val
                Nothing -> pure () -- should fail hard in this case?
              go rest
        go (Map.toList m)
  in  OrderedDict m <$> V.sequence aNew

