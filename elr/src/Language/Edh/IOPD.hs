module Language.Edh.IOPD where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad.ST (runST)
import qualified Data.HashMap.Strict as Map
import Data.Hashable (Hashable (hashWithSalt))
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Vector.Mutable (IOVector)
import qualified Data.Vector.Mutable as MV
import GHC.Conc (unsafeIOToSTM)
import Prelude

-- | A type with some value(s) triggering deletion semantics
class Deletable a where
  -- | Whether a value triggers deletion semantics when at right-hand-side of
  -- assignment
  impliesDeletionAtRHS :: a -> Bool

-- | All types contain no deletion triggering value by default,
-- but have an instance
instance {-# OVERLAPPABLE #-} Deletable t where
  impliesDeletionAtRHS _ = False

-- | Mutable dict with insertion order preserved
-- (Insertion Order Preserving Dict)
--
-- An iopd can only be mutated through STM monad, conflicts wrt concurrent
-- modifications are resolved automatically by STM retry
data IOPD k v where
  IOPD ::
    (Eq k, Hashable k, Deletable v) =>
    { iopd'map :: {-# UNPACK #-} !(TVar (Map.HashMap k Int)),
      iopd'write'pos :: {-# UNPACK #-} !(TVar Int),
      iopd'num'holes :: {-# UNPACK #-} !(TVar Int),
      -- use IOVector concerning immutable Vector to crash the program
      -- https://mail.haskell.org/pipermail/glasgow-haskell-users/2020-August/026947.html
      iopd'array :: {-# UNPACK #-} !(TVar (IOVector (TVar (Maybe (k, v)))))
    } ->
    IOPD k v

iopdClone ::
  forall k v. (Eq k, Hashable k, Deletable v) => IOPD k v -> STM (IOPD k v)
iopdClone (IOPD !mv !wpv !nhv !av) = do
  !mv' <- newTVar =<< readTVar mv
  !wpv' <- newTVar =<< readTVar wpv
  !nhv' <- newTVar =<< readTVar nhv
  !av' <-
    newTVar =<< do
      !a <- readTVar av
      unsafeIOToSTM $ MV.clone a
  return $ IOPD mv' wpv' nhv' av'

iopdTransform ::
  forall k v v'.
  (Eq k, Hashable k, Deletable v, Deletable v') =>
  (v -> v') ->
  IOPD k v ->
  STM (IOPD k v')
iopdTransform !trans (IOPD !mv !wpv !nhv !av) = do
  !mv' <- newTVar =<< readTVar mv
  !wp <- readTVar wpv
  !wpv' <- newTVar wp
  !nhv' <- newTVar =<< readTVar nhv
  !av' <-
    newTVar =<< do
      !a <- readTVar av
      !a' <- unsafeIOToSTM $ MV.unsafeNew (MV.length a)
      let go !i | i < 0 = return a'
          go !i = do
            unsafeIOToSTM (MV.unsafeRead a i) >>= readTVar >>= \case
              Nothing ->
                newTVar Nothing
                  >>= unsafeIOToSTM . MV.unsafeWrite a' i
              Just (!k, !v) ->
                newTVar (Just (k, trans v))
                  >>= unsafeIOToSTM . MV.unsafeWrite a' i
            go (i - 1)
      go (wp - 1)
  return $ IOPD mv' wpv' nhv' av'

iopdEmptyIO :: forall k v. (Eq k, Hashable k, Deletable v) => IO (IOPD k v)
iopdEmptyIO = do
  !mv <- newTVarIO Map.empty
  !wpv <- newTVarIO 0
  !nhv <- newTVarIO 0
  !av <- newTVarIO =<< MV.unsafeNew 0
  return $ IOPD mv wpv nhv av

iopdEmpty :: forall k v. (Eq k, Hashable k, Deletable v) => STM (IOPD k v)
iopdEmpty = do
  !mv <- newTVar Map.empty
  !wpv <- newTVar 0
  !nhv <- newTVar 0
  !av <- newTVar =<< unsafeIOToSTM (MV.unsafeNew 0)
  return $ IOPD mv wpv nhv av

iopdNull :: forall k v. (Eq k, Hashable k, Deletable v) => IOPD k v -> STM Bool
iopdNull (IOPD _mv !wpv !nhv _av) = do
  !wp <- readTVar wpv
  !nh <- readTVar nhv
  return (wp - nh <= 0)

iopdSize :: forall k v. (Eq k, Hashable k, Deletable v) => IOPD k v -> STM Int
iopdSize (IOPD _mv !wpv !nhv _av) = do
  !wp <- readTVar wpv
  !nh <- readTVar nhv
  return $ wp - nh

iopdInsert ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  k ->
  v ->
  IOPD k v ->
  STM ()
iopdInsert = iopdInsert' pure

iopdInsert' ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  (k -> STM k) ->
  k ->
  v ->
  IOPD k v ->
  STM ()
iopdInsert' !keyMap !key !val d@(IOPD !mv !wpv _nhv !av) =
  if impliesDeletionAtRHS val
    then iopdDelete' keyMap key d
    else doInsert
  where
    doInsert =
      keyMap key >>= \ !key' ->
        {- HLINT ignore "Redundant <$>" -}
        Map.lookup key' <$> readTVar mv >>= \case
          Just !i ->
            readTVar av >>= unsafeIOToSTM . flip MV.unsafeRead i
              >>= flip writeTVar (Just (key, val))
          Nothing -> do
            !entry <- newTVar $ Just (key, val)
            !wp0 <- readTVar wpv
            !a0 <- readTVar av
            if wp0 >= MV.length a0 then iopdReserve 7 d else pure ()
            !wp <- readTVar wpv
            !a <- readTVar av
            if wp >= MV.length a
              then error "bug: iopd reservation malfunctioned"
              else pure ()
            unsafeIOToSTM $ MV.unsafeWrite a wp entry
            modifyTVar' mv $ Map.insert key' wp
            writeTVar wpv (wp + 1)

iopdReserve ::
  forall k v. (Eq k, Hashable k, Deletable v) => Int -> IOPD k v -> STM ()
iopdReserve !moreCap (IOPD _mv !wpv _nhv !av) = do
  !wp <- readTVar wpv
  !a <- readTVar av
  let !needCap = wp + moreCap
      !cap = MV.length a
  if cap >= needCap
    then return ()
    else do
      !aNew <- unsafeIOToSTM $ do
        !a' <- MV.unsafeNew needCap
        MV.unsafeCopy (MV.unsafeSlice 0 wp a') (MV.unsafeSlice 0 wp a)
        return a'
      writeTVar av aNew

iopdUpdate ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  [(k, v)] ->
  IOPD k v ->
  STM ()
iopdUpdate = iopdUpdate' pure

iopdUpdate' ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  (k -> STM k) ->
  [(k, v)] ->
  IOPD k v ->
  STM ()
iopdUpdate' !keyMap !ps !d =
  if null ps
    then return ()
    else do
      iopdReserve (length ps) d
      upd ps
  where
    upd [] = return ()
    upd ((!key, !val) : rest) = do
      iopdInsert' keyMap key val d
      upd rest

iopdLookup ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  k ->
  IOPD k v ->
  STM (Maybe v)
iopdLookup = iopdLookup' pure

iopdLookup' ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  (k -> STM k) ->
  k ->
  IOPD k v ->
  STM (Maybe v)
iopdLookup' !keyMap !key (IOPD !mv _wpv _nhv !av) =
  keyMap key >>= \ !key' ->
    Map.lookup key' <$> readTVar mv >>= \case
      Nothing -> return Nothing
      Just !i ->
        (fmap snd <$>) $
          readTVar av >>= unsafeIOToSTM . flip MV.unsafeRead i
            >>= readTVar

iopdLookupDefault ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  v ->
  k ->
  IOPD k v ->
  STM v
iopdLookupDefault = iopdLookupDefault' pure

iopdLookupDefault' ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  (k -> STM k) ->
  v ->
  k ->
  IOPD k v ->
  STM v
iopdLookupDefault' !keyMap !defaultVal !key !iopd =
  iopdLookup' keyMap key iopd >>= \case
    Nothing -> return defaultVal
    Just !val -> return val

iopdDelete ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  k ->
  IOPD k v ->
  STM ()
iopdDelete = iopdDelete' pure

iopdDelete' ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  (k -> STM k) ->
  k ->
  IOPD k v ->
  STM ()
iopdDelete' !keyMap !key (IOPD !mv _wpv !nhv !av) =
  keyMap key >>= \ !key' ->
    Map.lookup key' <$> readTVar mv >>= \case
      Nothing -> return ()
      Just !i -> do
        readTVar av >>= unsafeIOToSTM . flip MV.unsafeRead i
          >>= flip writeTVar Nothing
        modifyTVar' nhv (+ 1)

iopdKeys :: forall k v. (Eq k, Hashable k, Deletable v) => IOPD k v -> STM [k]
iopdKeys (IOPD _mv !wpv _nhv !av) = do
  !wp <- readTVar wpv
  !a <- readTVar av
  let go !keys !i | i < 0 = return keys
      go !keys !i =
        unsafeIOToSTM (MV.unsafeRead a i) >>= readTVar >>= \case
          Nothing -> go keys (i - 1)
          Just (!key, _val) -> go (key : keys) (i - 1)
  go [] (wp - 1)

iopdValues :: forall k v. (Eq k, Hashable k, Deletable v) => IOPD k v -> STM [v]
iopdValues (IOPD _mv !wpv _nhv !av) = do
  !wp <- readTVar wpv
  !a <- readTVar av
  let go !vals !i | i < 0 = return vals
      go !vals !i =
        unsafeIOToSTM (MV.unsafeRead a i) >>= readTVar >>= \case
          Nothing -> go vals (i - 1)
          Just (_key, !val) -> go (val : vals) (i - 1)
  go [] (wp - 1)

iopdToList ::
  forall k v. (Eq k, Hashable k, Deletable v) => IOPD k v -> STM [(k, v)]
iopdToList (IOPD _mv !wpv _nhv !av) = do
  !wp <- readTVar wpv
  !a <- readTVar av
  let go !entries !i | i < 0 = return entries
      go !entries !i =
        unsafeIOToSTM (MV.unsafeRead a i) >>= readTVar >>= \case
          Nothing -> go entries (i - 1)
          Just !entry -> go (entry : entries) (i - 1)
  go [] (wp - 1)

iopdToReverseList ::
  forall k v. (Eq k, Hashable k, Deletable v) => IOPD k v -> STM [(k, v)]
iopdToReverseList (IOPD _mv !wpv _nhv !av) = do
  !wp <- readTVar wpv
  !a <- readTVar av
  let go !entries !i | i >= wp = return entries
      go !entries !i =
        unsafeIOToSTM (MV.unsafeRead a i) >>= readTVar >>= \case
          Nothing -> go entries (i + 1)
          Just !entry -> go (entry : entries) (i + 1)
  go [] 0

iopdFromList ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  [(k, v)] ->
  STM (IOPD k v)
iopdFromList = iopdFromList' pure

iopdFromList' ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  (k -> STM k) ->
  [(k, v)] ->
  STM (IOPD k v)
iopdFromList' !keyMap !entries = do
  !tves <-
    sequence $
      [ keyMap k >>= \ !k' ->
          if impliesDeletionAtRHS v
            then (k',True,) <$> newTVar Nothing
            else (k',False,) <$> newTVar (Just (k', v))
        | (!k, !v) <- entries
      ]
  (!mNew, !wpNew, !nhNew, !aNew) <- unsafeIOToSTM $ do
    !a <- MV.unsafeNew $ length entries
    let go [] !m !wp !nh = return (m, wp, nh, a)
        go ((!key, !del, !ev) : rest) !m !wp !nh =
          case Map.lookup key m of
            Nothing ->
              if del
                then go rest m wp nh
                else do
                  MV.unsafeWrite a wp ev
                  go rest (Map.insert key wp m) (wp + 1) nh
            Just !i -> do
              MV.unsafeWrite a i ev
              if del
                then go rest (Map.delete key m) wp (nh + 1)
                else go rest m wp nh
    go tves Map.empty 0 0
  !mv <- newTVar mNew
  !wpv <- newTVar wpNew
  !nhv <- newTVar nhNew
  !av <- newTVar aNew
  return $ IOPD mv wpv nhv av

iopdSnapshot ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  IOPD k v ->
  STM (OrderedDict k v)
iopdSnapshot (IOPD !mv !wpv _nhv !av) = do
  !m <- readTVar mv
  !wp <- readTVar wpv
  !a <- readTVar av
  !a' <- V.mapM readTVar =<< unsafeIOToSTM (V.freeze $ MV.unsafeSlice 0 wp a)
  return $ OrderedDict m a'

-- | Immutable dict with insertion order preserved
--
-- can be created either by 'odFromList', or taken as a snapshot of an IOPD
data OrderedDict k v where
  OrderedDict ::
    (Eq k, Hashable k, Deletable v) =>
    { od'map :: !(Map.HashMap k Int),
      od'array :: !(Vector (Maybe (k, v)))
    } ->
    OrderedDict k v

instance
  (Eq k, Hashable k, Eq v, Hashable v, Deletable v) =>
  Eq (OrderedDict k v)
  where
  x == y = odToList x == odToList y

instance
  (Eq k, Hashable k, Eq v, Hashable v, Deletable v) =>
  Hashable (OrderedDict k v)
  where
  hashWithSalt s od@(OrderedDict m _a) =
    s `hashWithSalt` m `hashWithSalt` odToList od

odTransform ::
  forall k v v'.
  (Eq k, Hashable k, Deletable v, Deletable v') =>
  (v -> v') ->
  OrderedDict k v ->
  OrderedDict k v'
odTransform !trans (OrderedDict !m !a) =
  OrderedDict m $ flip V.map a $ fmap $ \(!k, !v) -> (k, trans v)

odEmpty :: forall k v. (Eq k, Hashable k, Deletable v) => OrderedDict k v
odEmpty = OrderedDict Map.empty V.empty

odNull :: forall k v. (Eq k, Hashable k, Deletable v) => OrderedDict k v -> Bool
odNull (OrderedDict !m _a) = Map.null m

odSize :: forall k v. (Eq k, Hashable k, Deletable v) => OrderedDict k v -> Int
odSize (OrderedDict !m _a) = Map.size m

odLookup ::
  forall k v. (Eq k, Hashable k, Deletable v) => k -> OrderedDict k v -> Maybe v
odLookup !key (OrderedDict !m !a) = case Map.lookup key m of
  Nothing -> Nothing
  Just !i -> snd <$> V.unsafeIndex a i

odLookupDefault ::
  forall k v. (Eq k, Hashable k, Deletable v) => v -> k -> OrderedDict k v -> v
odLookupDefault !defaultVal !key !d = case odLookup key d of
  Nothing -> defaultVal
  Just !val -> val

odLookupDefault' ::
  forall k v v'.
  (Eq k, Hashable k, Deletable v) =>
  v' ->
  (v -> v') ->
  k ->
  OrderedDict k v ->
  v'
odLookupDefault' !defaultVal !f !key !d = case odLookup key d of
  Nothing -> defaultVal
  Just !val -> f val

odLookupContSTM ::
  forall k v v'.
  (Eq k, Hashable k, Deletable v) =>
  v' ->
  (v -> (v' -> STM ()) -> STM ()) ->
  k ->
  OrderedDict k v ->
  (v' -> STM ()) ->
  STM ()
odLookupContSTM !defaultVal !f !key !d !exit = case odLookup key d of
  Nothing -> exit defaultVal
  Just !val -> f val exit

odTakeOut ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  k ->
  OrderedDict k v ->
  (Maybe v, OrderedDict k v)
odTakeOut !key od@(OrderedDict !m !a) = case Map.lookup key m of
  Nothing -> (Nothing, od)
  Just !i -> (snd <$> V.unsafeIndex a i, OrderedDict (Map.delete key m) a)

odKeys :: forall k v. (Eq k, Hashable k, Deletable v) => OrderedDict k v -> [k]
odKeys (OrderedDict !m _a) = Map.keys m

odValues :: forall k v. (Eq k, Hashable k, Deletable v) => OrderedDict k v -> [v]
odValues (OrderedDict _m !a) = go [] (V.length a - 1)
  where
    go :: [v] -> Int -> [v]
    go !vals !i | i < 0 = vals
    go !vals !i = case V.unsafeIndex a i of
      Nothing -> go vals (i - 1)
      Just (_key, !val) -> go (val : vals) (i - 1)

odToList :: forall k v. (Eq k, Hashable k, Deletable v) => OrderedDict k v -> [(k, v)]
odToList (OrderedDict !m !a) = go [] (V.length a - 1)
  where
    go :: [(k, v)] -> Int -> [(k, v)]
    go !entries !i | i < 0 = entries
    go !entries !i = case V.unsafeIndex a i of
      Nothing -> go entries (i - 1)
      Just entry@(key, _val) ->
        if Map.member key m
          then go (entry : entries) (i - 1)
          else go entries (i - 1)

odToReverseList ::
  forall k v. (Eq k, Hashable k, Deletable v) => OrderedDict k v -> [(k, v)]
odToReverseList (OrderedDict !m !a) = go [] 0
  where
    !cap = V.length a
    go :: [(k, v)] -> Int -> [(k, v)]
    go !entries !i | i >= cap = entries
    go !entries !i = case V.unsafeIndex a i of
      Nothing -> go entries (i + 1)
      Just entry@(key, _val) ->
        if Map.member key m
          then go (entry : entries) (i + 1)
          else go entries (i + 1)

odFromList ::
  forall k v. (Eq k, Hashable k, Deletable v) => [(k, v)] -> OrderedDict k v
odFromList !entries =
  let (mNew, aNew) = runST $ do
        !a <- MV.unsafeNew $ length entries
        let go [] !m !wp =
              ((m,) . V.force <$>) $
                V.unsafeFreeze $ MV.unsafeSlice 0 wp a
            go (ev@(!key, !val) : rest) !m !wp =
              if impliesDeletionAtRHS val
                then case Map.lookup key m of
                  Nothing ->
                    go rest m wp
                  Just !i -> do
                    MV.unsafeWrite a i Nothing
                    go rest m wp
                else case Map.lookup key m of
                  Nothing -> do
                    MV.unsafeWrite a wp $ Just ev
                    go rest (Map.insert key wp m) (wp + 1)
                  Just !i -> do
                    MV.unsafeWrite a i $ Just ev
                    go rest m wp
        go entries Map.empty 0
   in OrderedDict mNew aNew

odInsert ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  k ->
  v ->
  OrderedDict k v ->
  OrderedDict k v
-- todo perf. optim.
odInsert k v d = odFromList $ odToList d ++ [(k, v)]

odUpdate ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  [(k, v)] ->
  OrderedDict k v ->
  OrderedDict k v
-- todo perf. optim.
odUpdate ul d = odFromList $ odToList d ++ ul

odUnion ::
  forall k v.
  (Eq k, Hashable k, Deletable v) =>
  OrderedDict k v ->
  OrderedDict k v ->
  OrderedDict k v
odUnion !d' !d = odFromList $ odToList d ++ odToList d'

odMap ::
  forall k v v'.
  (Eq k, Hashable k, Deletable v, Deletable v') =>
  (v -> v') ->
  OrderedDict k v ->
  OrderedDict k v'
odMap _f (OrderedDict !m _a) | Map.null m = OrderedDict Map.empty V.empty
odMap !f (OrderedDict !m !a) =
  let !aNew = runST $ do
        !a' <- MV.unsafeNew $ V.length a
        MV.set a' Nothing
        let go [] = V.unsafeFreeze a'
            go ((!key, !i) : rest) = do
              case V.unsafeIndex a i of
                Just (_, !val) -> MV.unsafeWrite a' i $ Just (key, f val)
                Nothing -> pure () -- should fail hard in this case?
              go rest
        go (Map.toList m)
   in OrderedDict m aNew

odMapSTM ::
  forall k v v'.
  (Eq k, Hashable k, Deletable v, Deletable v') =>
  (v -> STM v') ->
  OrderedDict k v ->
  STM (OrderedDict k v')
odMapSTM _f (OrderedDict !m _a)
  | Map.null m =
    return $ OrderedDict Map.empty V.empty
odMapSTM !f (OrderedDict !m !a) =
  let !aNew = runST $ do
        !a' <- MV.unsafeNew $ V.length a
        MV.set a' $ return Nothing
        let go [] = V.unsafeFreeze a'
            go ((!key, !i) : rest) = do
              case V.unsafeIndex a i of
                Just (_, !val) ->
                  MV.unsafeWrite a' i $ Just . (key,) <$> f val
                Nothing -> pure () -- should fail hard in this case?
              go rest
        go (Map.toList m)
   in OrderedDict m <$> V.sequence aNew

odMapContSTM ::
  forall k v v'.
  (Eq k, Hashable k, Deletable v, Deletable v') =>
  (v -> (v' -> STM ()) -> STM ()) ->
  OrderedDict k v ->
  (OrderedDict k v' -> STM ()) ->
  STM ()
odMapContSTM _f (OrderedDict !m _a) !exit
  | Map.null m =
    exit $ OrderedDict Map.empty V.empty
odMapContSTM !f (OrderedDict _m !a) !exit = toList (V.length a - 1) []
  where
    toList :: Int -> [(k, v')] -> STM ()
    toList !i !entries | i < 0 = exit $ odFromList entries
    toList !i !entries = case V.unsafeIndex a i of
      Nothing -> toList (i - 1) entries
      Just (!key, !val) ->
        f val $ \ !val' -> toList (i - 1) $ (key, val') : entries

odMapContSTM' ::
  forall k v v'.
  (Eq k, Hashable k, Deletable v, Deletable v') =>
  ((k, v) -> (v' -> STM ()) -> STM ()) ->
  OrderedDict k v ->
  (OrderedDict k v' -> STM ()) ->
  STM ()
odMapContSTM' _f (OrderedDict !m _a) !exit
  | Map.null m =
    exit $ OrderedDict Map.empty V.empty
odMapContSTM' !f (OrderedDict _m !a) !exit = toList (V.length a - 1) []
  where
    toList :: Int -> [(k, v')] -> STM ()
    toList !i !entries | i < 0 = exit $ odFromList entries
    toList !i !entries = case V.unsafeIndex a i of
      Nothing -> toList (i - 1) entries
      Just (!key, !val) ->
        f (key, val) $ \ !val' -> toList (i - 1) $ (key, val') : entries
