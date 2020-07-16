{-# LANGUAGE
    GADTs
  , TypeApplications
#-}

module Language.Edh.Details.RtTypes where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )
import           System.IO.Unsafe               ( unsafePerformIO )

import           Control.Monad.ST
import           Control.Monad.Except
import           Control.Monad.Reader

-- import           Control.Concurrent
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
import           Data.Vector.Mutable            ( IOVector )
import qualified Data.Vector.Mutable           as MV
import           Data.Dynamic

import           Text.Megaparsec

import           Data.Lossless.Decimal         as D

import           Language.Edh.Control


-- Boxed Vector for Edh values, non-transactional, mutable anytime
type EdhVector = IOVector EdhValue


-- | Similar to the insertion-order-preserving dict introduced since CPython
-- 3.6 (from PyPy), which is then formalized since the Python language 3.7,
-- but yet lacks much optimization.
--
-- Note: a nil (EdhNil) value in Edh has the special semantic of non-existence
data CompactDict k where
  CompactDict ::(Eq k, Hashable k) => {
      compact'dict'map :: !(Map.HashMap k Int)
    , compact'dict'write'pos :: !Int
    , compact'dict'num'holes :: !Int
    , compact'dict'array :: !(Vector (k, EdhValue))
    } -> CompactDict k
instance (Eq k, Hashable k) => Eq (CompactDict k) where
  -- todo perf optimization ?
  x == y = compactDictToList x == compactDictToList y
instance (Eq k, Hashable k) => Hashable (CompactDict k) where
  -- todo perf optimization ?
  hashWithSalt s x = hashWithSalt s $ compactDictToList x

compactDictEmpty :: forall k . (Eq k, Hashable k) => CompactDict k
compactDictEmpty = CompactDict Map.empty 0 0 V.empty

compactDictNull :: forall k . (Eq k, Hashable k) => CompactDict k -> Bool
compactDictNull (CompactDict _ !wp !nh _) = wp - nh <= 0

compactDictSize :: forall k . (Eq k, Hashable k) => CompactDict k -> Int
compactDictSize (CompactDict _ !wp !nh _) = wp - nh

compactDictSingleton
  :: forall k . (Eq k, Hashable k) => k -> EdhValue -> CompactDict k
compactDictSingleton !key !val =
  CompactDict (Map.singleton key 0) 1 0 $ V.singleton (key, val)

compactDictInsert
  :: forall k
   . (Eq k, Hashable k)
  => k
  -> EdhValue
  -> CompactDict k
  -> CompactDict k
compactDictInsert !key !val d@(CompactDict !m !wp !nh !y) =
  case Map.lookup key m of
    Nothing -> if wp >= cap
      then -- todo under certain circumstances, find a hole and fill it
        let !capNew = (cap +) $ max 7 $ quot cap 2
        in
          runST $ do
            !y'   <- MV.unsafeNew capNew
            !ySrc <- V.unsafeThaw y
            MV.unsafeCopy (MV.unsafeSlice 0 wp y') (MV.unsafeSlice 0 wp ySrc)
            flip MV.set (undefined, EdhNil)
              $ MV.unsafeSlice (wp + 1) (capNew - 1) y'
            MV.unsafeWrite y' wp (key, val)
            CompactDict (Map.insert @k key wp m) (wp + 1) nh
              <$> V.unsafeFreeze y'
      else runST $ do
        -- TODO concrrent mod is an issue with this impl. real harm be it ?
        y' <- V.unsafeThaw y
        MV.unsafeWrite y' wp (key, val)
        CompactDict (Map.insert key wp m) (wp + 1) nh <$> V.unsafeFreeze y'
    Just !i -> runST $ do -- copy-on-write
      y' <- V.thaw y
      MV.unsafeWrite y' i (key, val)
      y'' <- V.unsafeFreeze y'
      return d { compact'dict'array = y'' }
  where cap = V.length y

compactDictLookup
  :: forall k . (Eq k, Hashable k) => k -> CompactDict k -> Maybe EdhValue
compactDictLookup !key (CompactDict !m _ _ !y) = case Map.lookup key m of
  Nothing -> Nothing
  Just !i -> let (_, !val) = V.unsafeIndex y i in Just val

compactDictLookupDefault
  :: forall k
   . (Eq k, Hashable k)
  => EdhValue
  -> k
  -> CompactDict k
  -> EdhValue
compactDictLookupDefault !defVal !key (CompactDict !m _ _ !y) =
  case Map.lookup key m of
    Nothing -> defVal
    Just !i -> let (_, !val) = V.unsafeIndex y i in val

-- CAVEATS
--   the original dict will yield nil result, if looked up with the deleted key
compactDictUnsafeTakeOut
  :: forall k
   . (Eq k, Hashable k)
  => k
  -> CompactDict k
  -> (Maybe EdhValue, CompactDict k)
compactDictUnsafeTakeOut !key d@(CompactDict !m !wp !nh !y) =
  case Map.lookup key m of
    Nothing -> (Nothing, d)
    Just !i -> runST $ do
      let (_, !val) = V.unsafeIndex y i
      !y' <- V.unsafeThaw y
      MV.unsafeWrite y' i (key, EdhNil)
      !y'' <- V.unsafeFreeze y'
      return (Just val, CompactDict (Map.delete key m) wp (nh + 1) y'')

compactDictDelete
  :: forall k . (Eq k, Hashable k) => k -> CompactDict k -> CompactDict k
compactDictDelete !key d@(CompactDict !m !wp !nh !y) = case Map.lookup key m of
  Nothing -> d
  Just !i -> runST $ do -- copy-on-write
    y' <- V.thaw y
    MV.unsafeWrite y' i (undefined, EdhNil)
    CompactDict (Map.delete key m) wp (nh + 1) <$> V.unsafeFreeze y'

compactDictMap
  :: forall k
   . (Eq k, Hashable k)
  => (EdhValue -> EdhValue)
  -> CompactDict k
  -> CompactDict k
compactDictMap !f (CompactDict !m !wp !nh !y) =
  CompactDict m wp nh $ flip V.map y $ \e@(_, !val) ->
    if val /= EdhNil then (fst e, f val) else (undefined, EdhNil)

compactDictMapSTM
  :: forall k
   . (Eq k, Hashable k)
  => (EdhValue -> STM EdhValue)
  -> CompactDict k
  -> STM (CompactDict k)
compactDictMapSTM !f (CompactDict !m !wp !nh !y) = do
  let !y' = flip V.map y $ \e@(_, !val) -> if val /= EdhNil
        then (fst e, ) <$> f val
        else pure (undefined, EdhNil)
  y'' <- V.sequence y'
  return $ CompactDict m wp nh y''

compactDictKeys :: forall k . (Eq k, Hashable k) => CompactDict k -> [k]
compactDictKeys (CompactDict _m !wp _nh !y) = go [] (wp - 1)
 where
  go :: [k] -> Int -> [k]
  go keys !i | i < 0 = keys
  go keys !i =
    let entry@(_, !val) = V.unsafeIndex y i
    in  if val == EdhNil then go keys (i - 1) else go (fst entry : keys) (i - 1)

compactDictToList
  :: forall k . (Eq k, Hashable k) => CompactDict k -> [(k, EdhValue)]
compactDictToList (CompactDict _m !wp _nh !y) = go [] (wp - 1)
 where
  go :: [(k, EdhValue)] -> Int -> [(k, EdhValue)]
  go entries !i | i < 0 = entries
  go entries !i =
    let entry@(_, !val) = V.unsafeIndex y i
    in  if val == EdhNil
          then go entries (i - 1)
          else go (entry : entries) (i - 1)

compactDictFromList
  :: forall k . (Eq k, Hashable k) => [(k, EdhValue)] -> CompactDict k
compactDictFromList !entries = runST $ do
  !y <- MV.unsafeNew cap
  let go [] !m !wp !nh = do
        when (wp < cap) $ flip MV.set (undefined, EdhNil) $ MV.unsafeSlice
          wp
          (cap - wp)
          y
        CompactDict m wp nh <$> V.unsafeFreeze y
      go (e@(!k, !v) : es) !m !wp !nh = if v == EdhNil
        then case Map.lookup k m of
          Just !i -> do
            MV.unsafeWrite y i (undefined, EdhNil)
            go es (Map.delete k m) wp (nh + 1)
          Nothing -> go es m wp nh
        else case Map.lookup k m of
          Just !i -> do
            MV.unsafeWrite y i e
            go es m wp nh
          Nothing -> do
            MV.unsafeWrite y wp e
            go es (Map.insert k wp m) (wp + 1) nh
  go entries Map.empty 0 0
  where cap = length entries

compactDictUnion
  :: forall k
   . (Eq k, Hashable k)
  => CompactDict k
  -> CompactDict k
  -> CompactDict k
compactDictUnion d1 (CompactDict _ !wp2 !nh2 _) | wp2 - nh2 <= 0 = d1
compactDictUnion (CompactDict _ !wp1 !nh1 _) d2 | wp1 - nh1 <= 0 = d2
compactDictUnion (CompactDict _m1 !wp1 !nh1 !y1) (CompactDict _m2 !wp2 !nh2 !y2)
  = runST $ do
    !y <- MV.unsafeNew cap
    let go2 !m !i2 !wp | i2 >= wp2 = go1 m 0 wp
        go2 !m !i2 !wp             = do
          let e2@(key2, !val2) = V.unsafeIndex y2 i2
          if val2 == EdhNil
            then go2 m (i2 + 1) wp
            else case Map.lookup key2 m of
              Just !i -> do
                MV.unsafeWrite y i e2
                go2 m (i2 + 1) wp
              Nothing -> do
                MV.unsafeWrite y wp e2
                go2 (Map.insert key2 wp m) (i2 + 1) (wp + 1)
        go1 !m !i1 !wp | i1 >= wp1 = do
          when (wp < cap) $ flip MV.set (undefined, EdhNil) $ MV.unsafeSlice
            wp
            (cap - wp)
            y
          CompactDict m wp 0 <$> V.unsafeFreeze y
        go1 !m !i1 !wp = do
          let e1@(key1, !val1) = V.unsafeIndex y1 i1
          if val1 == EdhNil
            then go1 m (i1 + 1) wp
            else case Map.lookup key1 m of
              Just !i -> do
                MV.unsafeWrite y i e1
                go1 m (i1 + 1) wp
              Nothing -> do
                MV.unsafeWrite y wp e1
                go1 (Map.insert key1 wp m) (i1 + 1) (wp + 1)
    go2 Map.empty 0 0
  where !cap = (wp1 - nh1) + (wp2 - nh2)


-- | A pack of evaluated argument values with positional/keyword origin,
-- this works in places of tuples in other languages, apk in Edh can be
-- considered a tuple if only positional arguments inside.
-- Specifically, an empty apk is just considered an empty tuple.
data ArgsPack = ArgsPack {
    positional'args :: ![EdhValue]
    , keyword'args :: !(CompactDict AttrKey)
  } deriving (Eq)
instance Hashable ArgsPack where
  hashWithSalt s (ArgsPack !args !kwargs) =
    foldl' (\s' (k, v) -> s' `hashWithSalt` k `hashWithSalt` v)
           (foldl' hashWithSalt s args)
      $ compactDictToList kwargs
instance Show ArgsPack where
  show (ArgsPack !args kwargs) = if null args && compactDictNull kwargs
    then "()"
    else
      "( "
      ++ concat [ show i ++ ", " | i <- args ]
      ++ concat
           [ show kw ++ "=" ++ show v ++ ", "
           | (kw, v) <- compactDictToList kwargs
           ]
      ++ ")"


-- | A dict in Edh is neither an object nor an entity, but just a
-- mutable associative array.
data Dict = Dict !Unique !(TVar DictStore)
instance Eq Dict where
  Dict x'u _ == Dict y'u _ = x'u == y'u
instance Ord Dict where
  compare (Dict x'u _) (Dict y'u _) = compare x'u y'u
instance Hashable Dict where
  hashWithSalt s (Dict u _) = hashWithSalt s u
instance Show Dict where
  show (Dict _ d) = showEdhDict ds where ds = unsafePerformIO $ readTVarIO d
type ItemKey = EdhValue
type DictStore = CompactDict EdhValue

showEdhDict :: DictStore -> String
showEdhDict ds = if compactDictNull ds
  then "{}" -- no space should show in an empty dict
  else -- advocate trailing comma here
    "{ "
    ++ concat
         [ show k ++ ":" ++ show v ++ ", " | (k, v) <- compactDictToList ds ]
    ++ "}"

-- | create a new Edh dict from a properly typed hash map
createEdhDict :: DictStore -> STM EdhValue
createEdhDict !ds = do
  u <- unsafeIOToSTM newUnique
  EdhDict . Dict u <$> newTVar ds

-- | setting to `nil` value means deleting the item by the specified key
setDictItem :: ItemKey -> EdhValue -> DictStore -> DictStore
setDictItem !k v !ds = case v of
  EdhNil -> compactDictDelete k ds
  _      -> compactDictInsert k v ds

dictEntryList :: DictStore -> [EdhValue]
dictEntryList d = (<$> compactDictToList d)
  $ \(k, v) -> EdhArgsPack $ ArgsPack [k, v] compactDictEmpty


edhDictFromEntity :: EdhProgState -> Entity -> STM Dict
edhDictFromEntity pgs ent = do
  u  <- unsafeIOToSTM newUnique
  ps <- allEntityAttrs pgs ent
  (Dict u <$>) $ newTVar $ compactDictFromList
    [ (attrKeyValue k, v) | (k, v) <- ps ]

-- | An entity in Edh is the backing storage for a scope, with possibly 
-- an object (actually more objects still possible, but god forbid it)
-- mounted to it with one class and many supers.
--
-- An entity has attributes associated by 'AttrKey'.
data Entity = Entity {
    entity'ident :: !Unique
    , entity'store :: !(TVar Dynamic)
    , entity'man :: !EntityManipulater
  }
instance Eq Entity where
  Entity x'u _ _ == Entity y'u _ _ = x'u == y'u
instance Ord Entity where
  compare (Entity x'u _ _) (Entity y'u _ _) = compare x'u y'u
instance Hashable Entity where
  hashWithSalt s (Entity u _ _) = hashWithSalt s u

-- | Backing storage manipulation interface for entities
--
-- Arbitrary resources (esp. statically typed artifacts bearing high machine
-- performance purpose) can be wrapped as virtual entities through this interface.
data EntityManipulater = EntityManipulater {
    -- a result of `EdhNil` (i.e. `nil`) means no such attr, should usually lead
    -- to error;
    -- while an `EdhExpr _ (LitExpr NilLiteral) _` (i.e. `None` or `Nothing`)
    -- means knowingly absent, usually be okay and handled via pattern matching
    -- or equality test.
    lookup'entity'attr :: !(EdhProgState -> AttrKey -> Dynamic -> STM EdhValue)

    -- enumeration of attrs (this better be lazy)
    , all'entity'attrs :: !(EdhProgState -> Dynamic -> STM [(AttrKey, EdhValue)])

    -- single attr change
    , change'entity'attr :: !(EdhProgState -> AttrKey -> EdhValue -> Dynamic ->  STM Dynamic)

    -- bulk attr change
    , update'entity'attrs :: !(EdhProgState -> [(AttrKey, EdhValue)] -> Dynamic -> STM Dynamic)
  }

lookupEntityAttr :: EdhProgState -> Entity -> AttrKey -> STM EdhValue
lookupEntityAttr pgs (Entity _ !es !em) !k = do
  esd <- readTVar es
  lookup'entity'attr em pgs k esd
{-# INLINE lookupEntityAttr #-}

allEntityAttrs :: EdhProgState -> Entity -> STM [(AttrKey, EdhValue)]
allEntityAttrs pgs (Entity _ !es !em) = do
  esd <- readTVar es
  all'entity'attrs em pgs esd
{-# INLINE allEntityAttrs #-}

changeEntityAttr :: EdhProgState -> Entity -> AttrKey -> EdhValue -> STM ()
changeEntityAttr pgs (Entity _ !es !em) !k !v = do
  esd  <- readTVar es
  esd' <- change'entity'attr em pgs k v esd
  writeTVar es esd'
{-# INLINE changeEntityAttr #-}

updateEntityAttrs :: EdhProgState -> Entity -> [(AttrKey, EdhValue)] -> STM ()
updateEntityAttrs pgs (Entity _ !es !em) !ps = do
  esd  <- readTVar es
  esd' <- update'entity'attrs em pgs ps esd
  writeTVar es esd'
{-# INLINE updateEntityAttrs #-}

data AttrKey = AttrByName !AttrName | AttrBySym !Symbol
    deriving (Eq, Ord)
instance Show AttrKey where
  show (AttrByName attrName      ) = T.unpack attrName
  show (AttrBySym  (Symbol _ sym)) = T.unpack sym
instance Hashable AttrKey where
  hashWithSalt s (AttrByName name) =
    s `hashWithSalt` (0 :: Int) `hashWithSalt` name
  hashWithSalt s (AttrBySym sym) =
    s `hashWithSalt` (1 :: Int) `hashWithSalt` sym

type AttrName = Text

attrKeyValue :: AttrKey -> EdhValue
attrKeyValue (AttrByName nm ) = EdhString nm
attrKeyValue (AttrBySym  sym) = EdhSymbol sym


-- | Create a constantly empty entity - 冇
createMaoEntity :: STM Entity
createMaoEntity = do
  u  <- unsafeIOToSTM newUnique
  es <- newTVar $ toDyn EdhNil
  return $ Entity u es maoEntityManipulater

maoEntityManipulater :: EntityManipulater
maoEntityManipulater = EntityManipulater the'lookup'entity'attr
                                         the'all'entity'attrs
                                         the'change'entity'attr
                                         the'update'entity'attrs
 where
  the'lookup'entity'attr _ _ _ = return EdhNil
  the'all'entity'attrs _ _ = return []
  the'change'entity'attr _ _ _ = return  -- TODO raise error instead ?
  the'update'entity'attrs _ _ = return  -- TODO raise error instead ?


-- | Create an entity with an in-band 'Data.HashMap.Strict.HashMap'
-- as backing storage
createHashEntity :: CompactDict AttrKey -> STM Entity
createHashEntity !m = do
  u  <- unsafeIOToSTM newUnique
  es <- newTVar $ toDyn m
  return $ Entity u es hashEntityManipulater

hashEntityManipulater :: EntityManipulater
hashEntityManipulater = EntityManipulater the'lookup'entity'attr
                                          the'all'entity'attrs
                                          the'change'entity'attr
                                          the'update'entity'attrs
 where
  hm = flip fromDyn compactDictEmpty
  the'lookup'entity'attr _ !k =
    return . fromMaybe EdhNil . compactDictLookup k . hm
  the'all'entity'attrs _ = return . compactDictToList . hm
  the'change'entity'attr _ !k !v !d =
    let !ds = fromDyn d compactDictEmpty
    in  return $ toDyn $ case v of
          EdhNil -> compactDictDelete k ds
          _      -> compactDictInsert k v ds
  the'update'entity'attrs _ !ps =
    return . toDyn . compactDictUnion (compactDictFromList ps) . hm


-- | Create an entity with an out-of-band storage manipulater and an in-band
-- 'Dynamic' storage
createSideEntity :: EntityManipulater -> Dynamic -> STM Entity
createSideEntity !manip !esd = do
  u  <- unsafeIOToSTM newUnique
  es <- newTVar esd
  return $ Entity u es manip

-- | Create an entity manipulater with an out-of-band
-- 'Data.HashMap.Strict.HashMap' as backing storage
createSideEntityManipulater
  :: Bool -> [(AttrKey, EdhValue)] -> STM EntityManipulater
createSideEntityManipulater !writeProtected !arts = do
  obs <- newTVar $ compactDictFromList arts
  let the'lookup'entity'attr _ !k _ =
        fromMaybe EdhNil . compactDictLookup k <$> readTVar obs
      the'all'entity'attrs _ _ = compactDictToList <$> readTVar obs
      the'change'entity'attr pgs !k !v inband = if writeProtected
        then
          throwSTM
          $ EdhError UsageError "Writing a protected entity"
          $ getEdhCallContext 0 pgs
        else do
          modifyTVar' obs $ compactDictInsert k v
          return inband
      the'update'entity'attrs pgs !ps inband = if writeProtected
        then
          throwSTM
          $ EdhError UsageError "Writing a protected entity"
          $ getEdhCallContext 0 pgs
        else do
          modifyTVar' obs $ compactDictUnion (compactDictFromList ps)
          return inband
  return $ EntityManipulater the'lookup'entity'attr
                             the'all'entity'attrs
                             the'change'entity'attr
                             the'update'entity'attrs


-- | A symbol can stand in place of an alphanumeric name, used to
-- address an attribute from an object entity, but symbols are 
-- uniquely existing regardless however it is (alphanumerically)
-- named, this can be leveraged to solve naming clashes among
-- modules supplied by different parties.
--
-- And symbol values reside in a lexical outer scope are available
-- to its lexical inner scopes, e.g. a symbol bound to a module is
-- available to all procedures defined in the module, and a symbol
-- bound within a class procedure is available to all its methods
-- as well as nested classes.
data Symbol = Symbol !Unique !Text
instance Eq Symbol where
  Symbol x'u _ == Symbol y'u _ = x'u == y'u
instance Ord Symbol where
  compare (Symbol x'u _) (Symbol y'u _) = compare x'u y'u
instance Hashable Symbol where
  hashWithSalt s (Symbol u _) = hashWithSalt s u
instance Show Symbol where
  show (Symbol _ desc) = T.unpack desc

symbolName :: Symbol -> Text
symbolName (Symbol _ !desc) = case T.stripPrefix "@" desc of
  Nothing    -> desc
  Just !name -> name

globalSymbol :: Text -> Symbol
globalSymbol !description = unsafePerformIO $ do
  !u <- newUnique
  return $ Symbol u description
mkSymbol :: Text -> STM Symbol
mkSymbol !description = do
  !u <- unsafeIOToSTM newUnique
  return $ Symbol u description


-- | A list in Edh is a multable, singly-linked, prepend list.
data List = List !Unique !(TVar [EdhValue])
instance Eq List where
  List x'u _ == List y'u _ = x'u == y'u
instance Ord List where
  compare (List x'u _) (List y'u _) = compare x'u y'u
instance Hashable List where
  hashWithSalt s (List u _) = hashWithSalt s u
instance Show List where
  show (List _ !l) = if null ll
    then "[]"
    else "[ " ++ concat [ show i ++ ", " | i <- ll ] ++ "]"
    where ll = unsafePerformIO $ readTVarIO l


-- | The execution context of an Edh thread
data Context = Context {
    -- | the Edh world in context
    contextWorld :: !EdhWorld
    -- | the call stack frames of Edh procedures
    , callStack :: !(NonEmpty Scope)
    -- | the direct generator caller
    , generatorCaller :: !(Maybe EdhGenrCaller)
    -- | the match target value in context, normally be `true`, or the
    -- value from `x` in a `case x of` block
    , contextMatch :: EdhValue
    -- | currently executing statement
    , contextStmt :: !StmtSrc
    -- | whether it's discouraged for procedure definitions or similar
    -- expressions from installing their results as attributes into the
    -- context scope, i.e. the top of current call stack
    , contextPure :: !Bool
    -- | whether running within an exporting stmt
    , contextExporting :: !Bool
    -- | whether running within an effect stmt
    , contextEffDefining :: !Bool
  }
contextScope :: Context -> Scope
contextScope = NE.head . callStack
contextFrame :: Context -> Int -> Scope
contextFrame !ctx !unwind = unwindStack (NE.head stack) (NE.tail stack) unwind
 where
  !stack = callStack ctx
  unwindStack :: Scope -> [Scope] -> Int -> Scope
  unwindStack !s _ !c | c <= 0 = s
  unwindStack !s []         _  = s
  unwindStack _  (s : rest) !c = unwindStack s rest (c - 1)

type EdhGenrCaller
  = ( -- the caller's state
       EdhProgState
      -- the yield receiver, a.k.a. the caller's continuation
    ,  EdhValue -- one value yielded from the generator
    -> ( -- continuation of the genrator
        -- Left (pgsThrower, exv)
        --   exception to be thrown from that `yield` expr
        -- Right yieldedValue
        --   value given to that `yield` expr
        Either (EdhProgState, EdhValue) EdhValue -> STM ())
    -> EdhProc
    )


type EdhExcptHndlr
  =  EdhValue -- ^ the error value to handle
  -> (EdhValue -> EdhProc) -- ^ action to re-throw if not recovered
  -> EdhProc

defaultEdhExcptHndlr :: EdhExcptHndlr
defaultEdhExcptHndlr !exv !rethrow = rethrow exv


-- Especially note that Edh has no block scope as in C
-- family languages, JavaScript neither does before ES6,
-- Python neither does until now (2020).
--
-- There is only `procedure scope` in Edh
-- also see https://github.com/e-wrks/edh/Tour/#procedure
data Scope = Scope {
    -- | the entity of this scope, it's unique in a method procedure,
    -- and is the underlying entity of 'thisObject' in a class procedure.
    scopeEntity :: !Entity
    -- | `this` object in this scope
    , thisObject :: !Object
    -- | `that` object in this scope
    , thatObject :: !Object
    -- | the exception handler, `catch`/`finally` should capture the
    -- outer scope, and run its *tried* block with a new stack whose
    -- top frame is a scope all same but the `exceptionHandler` field,
    -- which executes its handling logics appropriately.
    , exceptionHandler :: !EdhExcptHndlr
    -- | the Edh procedure holding this scope
    , scopeProc :: !ProcDefi
    -- | the Edh stmt caused creation of this scope
    , scopeCaller :: !StmtSrc
    -- | when this scope is of an effectful procedure as called, this is the
    -- outer call stack from which (but not including the) scope the
    -- procedure is addressed of
    , effectsStack :: [Scope]
  }
instance Eq Scope where
  x == y = scopeEntity x == scopeEntity y
instance Ord Scope where
  compare x y = compare (scopeEntity x) (scopeEntity y)
instance Hashable Scope where
  hashWithSalt s x = hashWithSalt s (scopeEntity x)
instance Show Scope where
  show (Scope _ _ _ _ (ProcDefi _ _ _ (ProcDecl !addr _ !procBody)) (StmtSrc (!cPos, _)) _)
    = "📜 " ++ show addr ++ " 🔎 " ++ defLoc ++ " 👈 " ++ sourcePosPretty cPos
   where
    defLoc = case procBody of
      Right _                   -> "<host-code>"
      Left  (StmtSrc (dPos, _)) -> sourcePosPretty dPos

outerScopeOf :: Scope -> Maybe Scope
outerScopeOf = procedure'lexi . scopeProc

objectScope :: Context -> Object -> Scope
objectScope ctx obj = Scope { scopeEntity      = objEntity obj
                            , thisObject       = obj
                            , thatObject       = obj
                            , exceptionHandler = defaultEdhExcptHndlr
                            , scopeProc        = objClass obj
                            , scopeCaller      = contextStmt ctx
                            , effectsStack     = []
                            }

-- | An object views an entity, with inheritance relationship 
-- to any number of super objects.
data Object = Object {
    -- | the entity stores attribute set of the object
      objEntity :: !Entity
    -- | the class (a.k.a constructor) procedure of the object
    , objClass :: !ProcDefi
    -- | up-links for object inheritance hierarchy
    , objSupers :: !(TVar [Object])
  }
instance Eq Object where
  Object x'u _ _ == Object y'u _ _ = x'u == y'u
instance Ord Object where
  compare (Object x'u _ _) (Object y'u _ _) = compare x'u y'u
instance Hashable Object where
  hashWithSalt s (Object u _ _) = hashWithSalt s u
instance Show Object where
  -- it's not right to call 'atomically' here to read 'objSupers' for
  -- the show, as 'show' may be called from an stm transaction, stm
  -- will fail hard on encountering of nested 'atomically' calls.
  show (Object _ pd _) = "<object: " ++ T.unpack (procedureName pd) ++ ">"


-- | Read the entity store underlying an object
objStore :: Object -> STM Dynamic
objStore = readTVar . entity'store . objEntity

-- | Try cast and unveil an Object's storage of a known type
castObjectStore :: forall a . (Typeable a) => Object -> STM (Maybe a)
castObjectStore !obj = fromDynamic <$> objStore obj >>= \case
  Nothing  -> return Nothing
  Just !sv -> return $ Just sv
-- | Try cast and unveil a possible Object's storage of a known type
castObjectStore' :: forall a . (Typeable a) => EdhValue -> STM (Maybe a)
castObjectStore' !val = case edhUltimate val of
  EdhObject !obj -> castObjectStore obj
  _              -> return Nothing


-- | View an entity as object of specified class with specified ancestors
-- this is the black magic you want to avoid
viewAsEdhObject :: Entity -> Class -> [Object] -> STM Object
viewAsEdhObject !ent !cls !supers = Object ent cls <$> newTVar supers

-- | Clone an Edh object, with the specified function to clone the 'Dynamic'
-- entity store, while the 'EntityManipulater' is inherited.
--
-- CAVEATS:
--  *) the out-of-band storage if present, is referenced (via inherited 
--     'EntityManipulater') rather than copied
--  *) all super objects are referenced rather than deep copied
cloneEdhObject
  :: Object
  -> (Dynamic -> (Dynamic -> STM ()) -> STM ())
  -> (Object -> STM ())
  -> STM ()
cloneEdhObject (Object (Entity _ !esv !esm) !cls !supers) !esClone !exit =
  (readTVar esv >>=) $ flip esClone $ \ !esd' -> do
    !esv'    <- newTVar esd'
    !supers' <- newTVar =<< readTVar supers
    !u       <- unsafeIOToSTM newUnique
    exit $ Object (Entity u esv' esm) cls supers'


-- | A world for Edh programs to change
data EdhWorld = EdhWorld {
    -- | root scope of this world
    worldScope :: !Scope
    -- | all scope wrapper objects in this world belong to the same
    -- class as 'scopeSuper' and have it as the top most super,
    -- the bottom super of a scope wraper object is the original
    -- `this` object of that scope, thus an attr addressor can be
    -- used to read the attribute value out of the wrapped scope, when
    -- the attr name does not conflict with scope wrapper methods
    , scopeSuper :: !Object
    -- | all operators declared in this world, this also used as the
    -- _world lock_ in parsing source code to be executed in this world
    , worldOperators :: !(TMVar OpPrecDict)
    -- | all modules loaded or being loaded into this world, for each
    -- entry, will be a transient entry containing an error value (that
    -- appears as an EdhNamedValue) if failed loading, or a permanent
    -- entry containing the module object if successfully loaded
    , worldModules :: !(TMVar (Map.HashMap ModuleId (TMVar EdhValue)))
    -- | for console logging, input and output
    , worldConsole :: !EdhConsole
  }
instance Eq EdhWorld where
  EdhWorld x'root _ _ _ _ == EdhWorld y'root _ _ _ _ = x'root == y'root

type ModuleId = Text

worldContext :: EdhWorld -> Context
worldContext !world = Context
  { contextWorld       = world
  , callStack          = worldScope world :| []
  , generatorCaller    = Nothing
  , contextMatch       = true
  , contextStmt        = StmtSrc
                           ( SourcePos { sourceName   = "<genesis>"
                                       , sourceLine   = mkPos 1
                                       , sourceColumn = mkPos 1
                                       }
                           , VoidStmt
                           )
  , contextPure        = False
  , contextExporting   = False
  , contextEffDefining = False
  }
{-# INLINE worldContext #-}


-- | Checkout 'defaultEdhConsole' and 'defaultEdhIOLoop' from the
-- default batteries for implementation details, or just use that.
data EdhConsole = EdhConsole {
    consoleIO :: !(TBQueue EdhConsoleIO)
  , consoleIOLoop :: IO ()
  , consoleLogLevel :: !LogLevel
  , consoleLogger :: !EdhLogger
  , consoleFlush :: IO ()
  }
data EdhConsoleIO = ConsoleShutdown
    | ConsoleOut !Text -- ^ output a line
    | ConsoleIn !(TMVar EdhInput) !Text !Text
    -- ^ read input into the var, with ps1 ps2
    --   ps1 is single line prompt, ps2 for multil-line
  deriving (Eq)
data EdhInput = EdhInput {
    edh'input'src'name :: !Text
  , edh'input'1st'line :: !Int
  , edh'input'src'lines :: ![Text]
  } deriving (Eq, Show)
type EdhLogger = LogLevel -> Maybe String -> ArgsPack -> STM ()
type LogLevel = Int


-- | The ultimate nothingness (Chinese 无极/無極), i.e. <nothing> out of <chaos>
wuji :: EdhProgState -> OriginalValue
wuji !pgs = OriginalValue nil rootScope $ thisObject rootScope
  where rootScope = worldScope $ contextWorld $ edh'context pgs
{-# INLINE wuji #-}


-- | The monad for running of an Edh program
type EdhMonad = ReaderT EdhProgState STM
type EdhProc = EdhMonad (STM ())

-- | The states of a program
data EdhProgState = EdhProgState {
      edh'fork'queue :: !(TBQueue (EdhProgState, EdhProc))
    , edh'task'queue :: !(TBQueue EdhTask)
    , edh'perceivers :: !(TVar [PerceiveRecord])
    , edh'defers :: !(TVar [DeferRecord])
    , edh'in'tx :: !Bool
    , edh'context :: !Context
  }

type PerceiveRecord = (TChan EdhValue, EdhProgState, Expr)
type DeferRecord = (EdhProgState, EdhProc)

-- | Run an Edh proc from within STM monad
runEdhProc :: EdhProgState -> EdhProc -> STM ()
runEdhProc !pgs !p = join $ runReaderT p pgs
{-# INLINE runEdhProc #-}

-- | Continue an Edh proc with stm computation, there must be NO further
-- action following this statement, or the stm computation is just lost.
--
-- Note: this is just `return`, but procedures writen in the host language
-- (i.e. Haskell) with this instead of `return` will be more readable.
contEdhSTM :: STM () -> EdhProc
contEdhSTM = return
{-# INLINE contEdhSTM #-}

-- | Convenient function to be used as short-hand to return from an Edh
-- procedure (or functions with similar signature), this sets transaction
-- boundaries wrt tx stated in the program's current state.
exitEdhProc :: EdhProcExit -> EdhValue -> EdhProc
exitEdhProc !exit !val = ask >>= \pgs -> contEdhSTM $ exitEdhSTM pgs exit val
{-# INLINE exitEdhProc #-}
exitEdhProc' :: EdhProcExit -> OriginalValue -> EdhProc
exitEdhProc' !exit !result =
  ask >>= \pgs -> contEdhSTM $ exitEdhSTM' pgs exit result
{-# INLINE exitEdhProc' #-}

-- | Exit an stm computation to the specified Edh continuation
exitEdhSTM :: EdhProgState -> EdhProcExit -> EdhValue -> STM ()
exitEdhSTM !pgs !exit !val =
  let !scope  = contextScope $ edh'context pgs
      !result = OriginalValue { valueFromOrigin = val
                              , originScope     = scope
                              , originObject    = thatObject scope
                              }
  in  exitEdhSTM' pgs exit result
{-# INLINE exitEdhSTM #-}
exitEdhSTM' :: EdhProgState -> EdhProcExit -> OriginalValue -> STM ()
exitEdhSTM' !pgs !exit !result = if edh'in'tx pgs
  then join $ runReaderT (exit result) pgs
  else writeTBQueue (edh'task'queue pgs) $ EdhTxTask pgs result exit
{-# INLINE exitEdhSTM' #-}

-- | An Edh task record
data EdhTask where
  EdhTxTask ::{
      edh'task'pgs :: !EdhProgState
    , edh'task'input :: !OriginalValue
    , edh'task'job :: !(OriginalValue -> EdhProc)
    } -> EdhTask
  EdhSTMTask ::{
      edh'stm'pgs :: !EdhProgState
    , edh'stm'act :: !(STM a)
    , edh'stm'job :: !(a -> EdhProc)
    } -> EdhTask
  EdhIOTask ::{
      edh'io'pgs :: !EdhProgState
    , edh'io'act :: !(IO a)
    , edh'io'job :: !(a -> EdhProc)
    } -> EdhTask

-- | Type of an intrinsic infix operator in host language.
--
-- Note no stack frame is created/pushed when an intrinsic operator is called.
type EdhIntrinsicOp = Expr -> Expr -> EdhProcExit -> EdhProc

data IntrinOpDefi = IntrinOpDefi {
      intrinsic'op'uniq :: !Unique
    , intrinsic'op'symbol :: !AttrName
    , intrinsic'op :: EdhIntrinsicOp
  }

-- | Type of a procedure in host language that can be called from Edh code.
--
-- Note the top frame of the call stack from program state is the one for the
-- callee, that scope should have mounted the caller's scope entity, not a new
-- entity in contrast to when an Edh procedure as the callee.
type EdhProcedure -- such a procedure servs as the callee
  =  ArgsPack    -- ^ the pack of arguments
  -> EdhProcExit -- ^ the CPS exit to return a value from this procedure
  -> EdhProc

-- | The type for an Edh procedure's return, in continuation passing style.
type EdhProcExit = OriginalValue -> EdhProc

-- | An Edh value with the origin where it came from
data OriginalValue = OriginalValue {
    valueFromOrigin :: !EdhValue
    -- | the scope from which this value is addressed off
    , originScope :: !Scope
    -- | the attribute resolution target object in obtaining this value
    , originObject :: !Object
  }


-- | A no-operation as an Edh procedure, ignoring any arg
edhNop :: EdhProcedure
edhNop _ !exit = do
  pgs <- ask
  let scope = contextScope $ edh'context pgs
  exit $ OriginalValue nil scope $ thisObject scope

-- | A CPS exit serving end-of-procedure
edhEndOfProc :: EdhProcExit
edhEndOfProc _ = return $ return ()

-- | Construct an call context from program state
getEdhCallContext :: Int -> EdhProgState -> EdhCallContext
getEdhCallContext !unwind !pgs = EdhCallContext
  (T.pack $ sourcePosPretty tip)
  frames
 where
  unwindStack :: Int -> [Scope] -> [Scope]
  unwindStack c s | c <= 0 = s
  unwindStack _ []         = []
  unwindStack _ [f    ]    = [f]
  unwindStack c (_ : s)    = unwindStack (c - 1) s
  !ctx                = edh'context pgs
  (StmtSrc (!tip, _)) = contextStmt ctx
  !frames =
    foldl'
        (\sfs (Scope _ _ _ _ pd@(ProcDefi _ _ _ (ProcDecl _ _ !procBody)) (StmtSrc (!callerPos, _)) _) ->
          EdhCallFrame (procedureName pd)
                       (procSrcLoc procBody)
                       (T.pack $ sourcePosPretty callerPos)
            : sfs
        )
        []
      $ unwindStack unwind
      $ NE.init (callStack ctx)
  procSrcLoc :: Either StmtSrc EdhProcedure -> Text
  procSrcLoc !procBody = case procBody of
    Left  (StmtSrc (spos, _)) -> T.pack (sourcePosPretty spos)
    Right _                   -> "<host-code>"


-- | An event sink is similar to a Go channel, but is broadcast
-- in nature, in contrast to the unicast nature of channels in Go.
data EventSink = EventSink {
    evs'uniq :: !Unique
    -- | sequence number, increased on every new event posting.
    -- must read zero when no event has ever been posted to this sink,
    -- non-zero otherwise. monotonicly increasing most of the time,
    -- but allowed to wrap back to 1 when exceeded 'maxBound::Int'
    -- negative values can be used to indicate abnormal conditions.
    , evs'seqn :: !(TVar Int)
    -- | most recent value, not valid until evs'seqn turns non-zero
    , evs'mrv :: !(TVar EdhValue)
    -- | the broadcast channel
    , evs'chan :: !(TChan EdhValue)
    -- | subscriber counter
    , evs'subc :: !(TVar Int)
  }
instance Eq EventSink where
  EventSink x'u _ _ _ _ == EventSink y'u _ _ _ _ = x'u == y'u
instance Ord EventSink where
  compare (EventSink x'u _ _ _ _) (EventSink y'u _ _ _ _) = compare x'u y'u
instance Hashable EventSink where
  hashWithSalt s (EventSink s'u _ _ _ _) = hashWithSalt s s'u
instance Show EventSink where
  show EventSink{} = "<sink>"


-- Atop Haskell, most types in Edh the surface language, are for
-- immutable values, besides dict and list, the only other mutable
-- data structure in Edh, is the entity, an **entity** is a set of
-- mutable attributes.
--
-- After applied a set of rules/constraints about how attributes
-- of an entity can be retrived and altered, it becomes an object.
--
-- Theoretically an entity is not necessarily mandated to have an
-- `identity` attribute among others, while practically the memory
-- address for physical storage of the attribute set, naturally
-- serves an `identity` attribute in single-process + single-run
-- scenario. Distributed programs, especially using a separate
-- database for storage, will tend to define a generated UUID 
-- attribute or the like.

-- | everything in Edh is a value
data EdhValue =
  -- | type itself is a kind of (immutable) value
      EdhType !EdhTypeValue
  -- | end values (immutable)
    | EdhNil
    | EdhDecimal !Decimal
    | EdhBool !Bool
    | EdhBlob !ByteString
    | EdhString !Text
    | EdhSymbol !Symbol

  -- | direct pointer (to entities) values
    | EdhObject !Object

  -- | mutable containers
    | EdhDict !Dict
    | EdhList !List

  -- | immutable containers
  --   the elements may still pointer to mutable data
    | EdhPair !EdhValue !EdhValue
    | EdhArgsPack ArgsPack

  -- executable precedures
    | EdhIntrOp !Precedence !IntrinOpDefi
    | EdhClass !ProcDefi
    | EdhMethod !ProcDefi
    | EdhOprtor !Precedence !(Maybe EdhValue) !ProcDefi
    | EdhGnrtor !ProcDefi
    | EdhIntrpr !ProcDefi
    | EdhPrducr !ProcDefi

  -- similar to Python Descriptor
  -- with a getter method and optionally a settor method, for properties
  -- (programmatically managed attributes) to be defined on objects
  -- deleter semantic is expressed as calling setter without arg
    | EdhDescriptor !ProcDefi !(Maybe ProcDefi)

  -- * flow control
    | EdhBreak
    | EdhContinue
    | EdhCaseClose !EdhValue
    | EdhCaseOther
    | EdhFallthrough
    | EdhRethrow
    | EdhYield !EdhValue
    | EdhReturn !EdhValue
  -- | prefer better efforted result, but can default to the specified value
  -- if none applicable
  -- TODO use this in place of { continue } to signal try-next-impl semantics
  --      similar to NotImplemented in Python. may enable the syntax of
  --  `return default <expr>` for impls as Edh procedures, i.e. `default` to
  --      be a keyword forming `DefaultExpr !Expr` expression.
  --
  --      then `return default { continue }` can be used to signal that it's
  --      not implemented at all, as current semantic, after that the branch
  --      will be able to eval to `{ continue }` without rendering the (->)
  --      operator as considered not implemented.
    | EdhDefault !EdhValue

  -- | event sink
    | EdhSink !EventSink

  -- | named value, a.k.a. term definition
    | EdhNamedValue !AttrName !EdhValue

  -- | reflective expr, with source (or not, if empty)
    | EdhExpr !Unique !Expr !Text

instance Show EdhValue where
  show (EdhType t)     = show t
  show EdhNil          = "nil"
  show (EdhDecimal v ) = showDecimal v
  show (EdhBool    v ) = if v then "true" else "false"
  show (EdhBlob    b ) = "<blob#" <> show (B.length b) <> ">"
  show (EdhString  v ) = show v
  show (EdhSymbol  v ) = show v

  show (EdhObject  v ) = show v

  show (EdhDict    v ) = show v
  show (EdhList    v ) = show v

  show (EdhPair k v  ) = show k <> ":" <> show v
  show (EdhArgsPack v) = show v

  show (EdhIntrOp !preced (IntrinOpDefi _ !opSym _)) =
    "<intrinsic: (" ++ T.unpack opSym ++ ") " ++ show preced ++ ">"
  show (EdhClass  !pd) = T.unpack (procedureName pd)
  show (EdhMethod !pd) = T.unpack (procedureName pd)
  show (EdhOprtor !preced _ !pd) =
    "<operator: (" ++ T.unpack (procedureName pd) ++ ") " ++ show preced ++ ">"
  show (EdhGnrtor !pd) = T.unpack (procedureName pd)
  show (EdhIntrpr !pd) = T.unpack (procedureName pd)
  show (EdhPrducr !pd) = T.unpack (procedureName pd)

  show (EdhDescriptor !getter !setter) =
    (<> T.unpack (procedureName getter) <> ">") $ case setter of
      Nothing -> "<readonly property "
      Just _  -> "<property "

  show EdhBreak         = "<break>"
  show EdhContinue      = "<continue>"
  show (EdhCaseClose v) = "<caseclose: " ++ show v ++ ">"
  show EdhCaseOther     = "<caseother>"
  show EdhFallthrough   = "<fallthrough>"
  show EdhRethrow       = "<rethrow>"
  show (EdhYield   v)   = "<yield: " ++ show v ++ ">"
  show (EdhReturn  v)   = "<return: " ++ show v ++ ">"
  show (EdhDefault v)   = "<default: " ++ show v ++ ">"

  show (EdhSink    v)   = show v

  show (EdhNamedValue n v@EdhNamedValue{}) =
    -- Edh operators are all left-associative, parenthesis needed
    T.unpack n <> " := (" <> show v <> ")"
  show (EdhNamedValue n v) = T.unpack n <> " := " <> show v

  show (EdhExpr _ x s    ) = if T.null s
    then -- source-less form
         "<expr: " ++ show x ++ ">"
    else -- source-ful form
         T.unpack s

-- Note:
--
-- here is identity-wise equality i.e. pointer equality if mutable,
-- or value equality if immutable.
--
-- the semantics are different from value-wise equality especially
-- for types of:  object/dict/list

instance Eq EdhValue where
  EdhType x       == EdhType y       = x == y
  EdhNil          == EdhNil          = True
  EdhDecimal x    == EdhDecimal y    = x == y
  EdhBool    x    == EdhBool    y    = x == y
  EdhBlob    x    == EdhBlob    y    = x == y
  EdhString  x    == EdhString  y    = x == y
  EdhSymbol  x    == EdhSymbol  y    = x == y

  EdhObject  x    == EdhObject  y    = x == y

  EdhDict    x    == EdhDict    y    = x == y
  EdhList    x    == EdhList    y    = x == y
  EdhPair x'k x'v == EdhPair y'k y'v = x'k == y'k && x'v == y'v
  EdhArgsPack x   == EdhArgsPack y   = x == y

  EdhIntrOp _ (IntrinOpDefi x'u _ _) == EdhIntrOp _ (IntrinOpDefi y'u _ _) =
    x'u == y'u
  EdhClass  x     == EdhClass  y     = x == y
  EdhMethod x     == EdhMethod y     = x == y
  EdhOprtor _ _ x == EdhOprtor _ _ y = x == y
  EdhGnrtor x     == EdhGnrtor y     = x == y
  EdhIntrpr x     == EdhIntrpr y     = x == y
  EdhPrducr x     == EdhPrducr y     = x == y

  EdhDescriptor x'getter x'setter == EdhDescriptor y'getter y'setter =
    x'getter == y'getter && x'setter == y'setter

  EdhBreak                    == EdhBreak                    = True
  EdhContinue                 == EdhContinue                 = True
  EdhCaseClose x              == EdhCaseClose y              = x == y
  EdhCaseOther                == EdhCaseOther                = True
  EdhFallthrough              == EdhFallthrough              = True
  EdhRethrow                  == EdhRethrow                  = True
-- todo: regard a yielded/returned value equal to the value itself ?
  EdhYield   x'v              == EdhYield   y'v              = x'v == y'v
  EdhReturn  x'v              == EdhReturn  y'v              = x'v == y'v
  EdhDefault x'v              == EdhDefault y'v              = x'v == y'v

  EdhSink    x                == EdhSink    y                = x == y

  EdhNamedValue _ x'v         == EdhNamedValue _ y'v         = x'v == y'v
  EdhNamedValue _ x'v         == y                           = x'v == y
  x                           == EdhNamedValue _ y'v         = x == y'v

  EdhExpr _   (LitExpr x'l) _ == EdhExpr _   (LitExpr y'l) _ = x'l == y'l
  EdhExpr x'u _             _ == EdhExpr y'u _             _ = x'u == y'u

-- todo: support coercing equality ?
--       * without this, we are a strongly typed dynamic language
--       * with this, we'll be a weakly typed dynamic language
  _                           == _                           = False

instance Hashable EdhValue where
  hashWithSalt s (EdhType x) = hashWithSalt s $ 1 + fromEnum x
  hashWithSalt s EdhNil = hashWithSalt s (0 :: Int)
  hashWithSalt s (EdhDecimal x                      ) = hashWithSalt s x
  hashWithSalt s (EdhBool    x                      ) = hashWithSalt s x
  hashWithSalt s (EdhBlob    x                      ) = hashWithSalt s x
  hashWithSalt s (EdhString  x                      ) = hashWithSalt s x
  hashWithSalt s (EdhSymbol  x                      ) = hashWithSalt s x
  hashWithSalt s (EdhObject  x                      ) = hashWithSalt s x

  hashWithSalt s (EdhDict    x                      ) = hashWithSalt s x
  hashWithSalt s (EdhList    x                      ) = hashWithSalt s x
  hashWithSalt s (EdhPair k v) = s `hashWithSalt` k `hashWithSalt` v
  hashWithSalt s (EdhArgsPack x                     ) = hashWithSalt s x

  hashWithSalt s (EdhIntrOp _ (IntrinOpDefi x'u _ _)) = hashWithSalt s x'u
  hashWithSalt s (EdhClass  x                       ) = hashWithSalt s x
  hashWithSalt s (EdhMethod x                       ) = hashWithSalt s x
  hashWithSalt s (EdhOprtor _ _ x                   ) = hashWithSalt s x
  hashWithSalt s (EdhGnrtor x                       ) = hashWithSalt s x
  hashWithSalt s (EdhIntrpr x                       ) = hashWithSalt s x
  hashWithSalt s (EdhPrducr x                       ) = hashWithSalt s x

  hashWithSalt s (EdhDescriptor getter setter) =
    s `hashWithSalt` getter `hashWithSalt` setter

  hashWithSalt s EdhBreak    = hashWithSalt s (-1 :: Int)
  hashWithSalt s EdhContinue = hashWithSalt s (-2 :: Int)
  hashWithSalt s (EdhCaseClose v) =
    s `hashWithSalt` (-3 :: Int) `hashWithSalt` v
  hashWithSalt s EdhCaseOther              = hashWithSalt s (-4 :: Int)
  hashWithSalt s EdhFallthrough            = hashWithSalt s (-5 :: Int)
  hashWithSalt s EdhRethrow                = hashWithSalt s (-6 :: Int)
  hashWithSalt s (EdhYield v) = s `hashWithSalt` (-7 :: Int) `hashWithSalt` v
  hashWithSalt s (EdhReturn v) = s `hashWithSalt` (-8 :: Int) `hashWithSalt` v
  hashWithSalt s (EdhDefault v) = s `hashWithSalt` (-9 :: Int) `hashWithSalt` v

  hashWithSalt s (EdhSink    x           ) = hashWithSalt s x

  hashWithSalt s (EdhNamedValue _ v      ) = hashWithSalt s v

  hashWithSalt s (EdhExpr _ (LitExpr l) _) = hashWithSalt s l
  hashWithSalt s (EdhExpr u _           _) = hashWithSalt s u


edhDeCaseClose :: EdhValue -> EdhValue
edhDeCaseClose (EdhCaseClose !val) = edhDeCaseClose val
edhDeCaseClose !val                = val

edhUltimate :: EdhValue -> EdhValue
edhUltimate (EdhNamedValue _ v) = edhDeCaseClose v
edhUltimate (EdhReturn  v     ) = edhDeCaseClose v
edhUltimate (EdhDefault v     ) = edhDeCaseClose v
edhUltimate (EdhYield   v     ) = edhDeCaseClose v
edhUltimate v                   = edhDeCaseClose v


nil :: EdhValue
nil = EdhNil

-- | Resembles `None` as in Python
--
-- assigning to `nil` in Edh is roughly the same of `delete` as
-- in JavaScript, and `del` as in Python. Assigning to `None`
-- will keep the dict entry or object attribute while still
-- carrying a semantic of *absence*.
edhNone :: EdhValue
edhNone = EdhNamedValue "None" EdhNil

-- | None as an expression
edhNoneExpr :: Expr
edhNoneExpr =
  InfixExpr ":=" (AttrExpr (DirectRef (NamedAttr "None"))) (LitExpr NilLiteral)

-- | Similar to `None`
--
-- though we don't have `Maybe` monad in Edh, having a `Nothing`
-- carrying null semantic may be useful in some cases.
edhNothing :: EdhValue
edhNothing = EdhNamedValue "Nothing" EdhNil

-- | Nothing as an expression
edhNothingExpr :: Expr
edhNothingExpr = InfixExpr ":="
                           (AttrExpr (DirectRef (NamedAttr "Nothing")))
                           (LitExpr NilLiteral)

-- | With `nil` converted to `None` so the result will never be `nil`.
--
-- As `nil` carries *delete* semantic in assignment, in some cases it's better
-- avoided.
noneNil :: EdhValue -> EdhValue
noneNil EdhNil = edhNone
noneNil !v     = v

nan :: EdhValue
nan = EdhDecimal D.nan

inf :: EdhValue
inf = EdhDecimal D.inf

true :: EdhValue
true = EdhBool True

false :: EdhValue
false = EdhBool False


newtype StmtSrc = StmtSrc (SourcePos, Stmt)
instance Eq StmtSrc where
  StmtSrc (x'sp, _) == StmtSrc (y'sp, _) = x'sp == y'sp
instance Show StmtSrc where
  show (StmtSrc (_sp, stmt)) = show stmt


data Stmt =
      -- | literal `pass` to fill a place where a statement needed,
      -- same as in Python
      VoidStmt
      -- | atomically isolated, mark a code section for transaction bounds
    | AtoIsoStmt !Expr
      -- | similar to `go` in Go, starts goroutine
    | GoStmt !Expr
      -- | not similar to `defer` in Go (in Go `defer` snapshots arg values
      -- and schedules execution on func return), but in Edh `defer`
      -- schedules execution on thread termination
    | DeferStmt !Expr
      -- | artifacts introduced within an `effect` statement will be put
      -- into effect namespace, which as currently implemented, a dict
      -- resides in current scope entity addressed by name `__exports__`
    | EffectStmt !Expr
      -- | assignment with args (un/re)pack sending/receiving syntax
    | LetStmt !ArgsReceiver !ArgsPacker
      -- | super object declaration for a descendant object
    | ExtendsStmt !Expr
      -- | perceiption declaration, a perceiver is bound to an event `sink`
      -- with the calling thread as context, when an event fires from that
      -- event `sink`, the bound perceiver body will be executed from the
      -- thread where it's declared, after the currernt transaction on that
      -- thread finishes, a perceiver body can `break` to terminate that
      -- particular thread, or the thread will continue to process next
      -- perceiver, if no perceiver does `break`, next transactional task
      -- is carried on as normally.
      --
      -- the perceiver body uses a value/pattern matching branch, or a
      -- group of branches (as a block expr) to handle the happened event
      -- data, including `nil` as end-of-stream indicator.
      --
      -- the perceiption construct is somewhat similar to traditional signal
      -- handling mechanism in OS process management
    | PerceiveStmt !Expr !Expr
      -- | while loop
    | WhileStmt !Expr !StmtSrc
      -- | break from a while/for loop, or terminate the Edh thread if given
      -- from a perceiver
    | BreakStmt
      -- | continue a while/for loop
    | ContinueStmt
      -- | similar to fallthrough in Go
    | FallthroughStmt
      -- | rethrow current exception
    | RethrowStmt
      -- | any value can be thrown as exception, handling will rely on the
      --   ($=>) as `catch` and (@=>) as `finally` operators
    | ThrowStmt !Expr
      -- | early stop from a procedure
    | ReturnStmt !Expr
      -- | expression with precedence
    | ExprStmt !Expr
  deriving (Show)

-- Attribute addressor
data AttrAddr = ThisRef | ThatRef | SuperRef
    | DirectRef !AttrAddressor
    | IndirectRef !Expr !AttrAddressor
  deriving (Eq, Show)

-- | the key to address attributes against a left hand entity object or
-- current scope
data AttrAddressor =
    -- | vanilla form, by alphanumeric name
    NamedAttr !AttrName
    -- | get the symbol value from current scope,
    -- then use it to address attributes
    | SymbolicAttr !AttrName
  deriving (Eq)
instance Show AttrAddressor where
  show (NamedAttr    n) = T.unpack n
  show (SymbolicAttr s) = "@" <> T.unpack s
instance Hashable AttrAddressor where
  hashWithSalt s (NamedAttr name) = s `hashWithSalt` name
  hashWithSalt s (SymbolicAttr sym) =
    s `hashWithSalt` ("@" :: Text) `hashWithSalt` sym


receivesNamedArg :: Text -> ArgsReceiver -> Bool
receivesNamedArg _     WildReceiver              = True
receivesNamedArg !name (SingleReceiver argRcvr ) = _hasNamedArg name [argRcvr]
receivesNamedArg !name (PackReceiver   argRcvrs) = _hasNamedArg name argRcvrs

_hasNamedArg :: Text -> [ArgReceiver] -> Bool
_hasNamedArg _     []           = False
_hasNamedArg !name (arg : rest) = case arg of
  RecvArg (NamedAttr !argName) _ _ -> argName == name || _hasNamedArg name rest
  _ -> _hasNamedArg name rest

data ArgsReceiver = PackReceiver ![ArgReceiver]
    | SingleReceiver !ArgReceiver
    | WildReceiver
  deriving (Eq)
instance Show ArgsReceiver where
  show (PackReceiver   rs) = "( " ++ unwords ((++ ", ") . show <$> rs) ++ ")"
  show (SingleReceiver r ) = "(" ++ show r ++ ")"
  show WildReceiver        = "*"

data ArgReceiver = RecvRestPosArgs !AttrName
    | RecvRestKwArgs !AttrName
    | RecvRestPkArgs !AttrName
    | RecvArg !AttrAddressor !(Maybe AttrAddr) !(Maybe Expr)
  deriving (Eq)
instance Show ArgReceiver where
  show (RecvRestPosArgs nm) = "*" ++ T.unpack nm
  show (RecvRestKwArgs  nm) = "**" ++ T.unpack nm
  show (RecvRestPkArgs  nm) = "***" ++ T.unpack nm
  show (RecvArg nm _ _    ) = show nm

mandatoryArg :: AttrName -> ArgReceiver
mandatoryArg !name = RecvArg (NamedAttr name) Nothing Nothing

optionalArg :: AttrName -> Expr -> ArgReceiver
optionalArg !name !defExpr = RecvArg (NamedAttr name) Nothing (Just defExpr)


type ArgsPacker = [ArgSender]
data ArgSender = UnpackPosArgs !Expr
    | UnpackKwArgs !Expr
    | UnpackPkArgs !Expr
    | SendPosArg !Expr
    | SendKwArg !AttrAddressor !Expr
  deriving (Eq, Show)

-- | Procedure declaration, result of parsing
data ProcDecl = ProcDecl {
      procedure'addr :: !AttrAddressor
    , procedure'args :: !ArgsReceiver
    , procedure'body :: !(Either StmtSrc EdhProcedure)
  }
instance Eq ProcDecl where
  ProcDecl{} == ProcDecl{} = False
instance Show ProcDecl where
  show (ProcDecl !addr _ !pb) = case pb of
    Left  _ -> "<edh-proc " <> show addr <> ">"
    Right _ -> "<host-proc " <> show addr <> ">"


-- | Procedure definition, result of execution of the declaration
data ProcDefi = ProcDefi {
    procedure'uniq :: !Unique
    , procedure'name :: !AttrKey
    , procedure'lexi :: !(Maybe Scope)
    , procedure'decl :: {-# UNPACK #-} !ProcDecl
  }
instance Eq ProcDefi where
  ProcDefi x'u _ _ _ == ProcDefi y'u _ _ _ = x'u == y'u
instance Ord ProcDefi where
  compare (ProcDefi x'u _ _ _) (ProcDefi y'u _ _ _) = compare x'u y'u
instance Hashable ProcDefi where
  hashWithSalt s (ProcDefi u _ scope _) =
    s `hashWithSalt` u `hashWithSalt` scope
instance Show ProcDefi where
  show (ProcDefi _ !name _ (ProcDecl !addr _ !pb)) = case pb of
    Left  _ -> "<edh-proc " <> show name <> " : " <> show addr <> ">"
    Right _ -> "<host-proc " <> show name <> " : " <> show addr <> ">"

procedureName :: ProcDefi -> Text
procedureName (ProcDefi _ !name _ _) = T.pack $ show name

lexicalScopeOf :: ProcDefi -> Scope
lexicalScopeOf (ProcDefi _ _ (Just scope) _) = scope
lexicalScopeOf (ProcDefi _ _ Nothing _) =
  error "bug: asking for scope of world root"


-- | The Edh class is a special type of procedure, receives no argument.
type Class = ProcDefi


data Prefix = PrefixPlus | PrefixMinus | Not
    -- | to disregard the match target in context,
    -- for a branch condition
    | Guard
  deriving (Eq, Show)

data DictKeyExpr =
      LitDictKey !Literal
    | AddrDictKey !AttrAddr
    | ExprDictKey !Expr -- this must be quoted in parenthesis
  deriving (Eq, Show)

data Expr = LitExpr !Literal | PrefixExpr !Prefix !Expr
    | IfExpr { if'condition :: !Expr
            , if'consequence :: !Expr
            , if'alternative :: !(Maybe Expr)
            }
    | CaseExpr { case'target :: !Expr , case'branches :: !Expr }

      -- note: the order of entries is reversed as parsed from source
    | DictExpr ![(DictKeyExpr, Expr)]
    | ListExpr ![Expr]
    | ArgsPackExpr !ArgsPacker
    | ParenExpr !Expr

      -- | import with args (re)pack receiving syntax
      -- `into` a target object from specified expr, or current scope
    | ImportExpr !ArgsReceiver !Expr !(Maybe Expr)
      -- | only artifacts introduced within an `export` statement, into
      -- `this` object in context, are eligible for importing by others
    | ExportExpr !Expr
      -- | namespace object creation
    | NamespaceExpr !ProcDecl !ArgsPacker
      -- | class (constructor) procedure definition
    | ClassExpr !ProcDecl
      -- | method procedure definition
    | MethodExpr !ProcDecl
      -- | generator procedure definition
    | GeneratorExpr !ProcDecl
      -- | interpreter declaration, an interpreter procedure is not otherwise
      -- different from a method procedure, except it receives arguments
      -- in expression form rather than values, in addition to the reflective
      -- `callerScope` as first argument
    | InterpreterExpr !ProcDecl
    | ProducerExpr !ProcDecl
      -- | operator declaration
    | OpDeclExpr !OpSymbol !Precedence !ProcDecl
      -- | operator override
    | OpOvrdExpr !OpSymbol !ProcDecl !Precedence

    -- | the block is made an expression in Edh, instead of a statement
    -- as in a C family language. it evaluates to the value of last expr
    -- within it, in case no `EdhCaseClose` encountered, or can stop
    -- early with the value from a `EdhCaseClose`, typically returned
    -- from the branch `(->)` operator.
    --
    -- this allows multiple statements grouped as a single expression
    -- fitting into subclauses of if-then-else, while, for-from-do,
    -- and try-catch-finally etc. where an expression is expected.
    -- 
    -- then the curly brackets can be used to quote a statement into an
    -- expression, e.g. so that a method procedure can explicitly
    -- `return { continue }` to carry a semantic to the magic method
    -- caller that it should try next method, similar to what
    -- `NotImplemented` does in Python.
    | BlockExpr ![StmtSrc]

    | YieldExpr !Expr

    -- | a for-from-do loop is made an expression in Edh, so it can
    -- appear as the right-hand expr of the comprehension (=<) operator.
    | ForExpr !ArgsReceiver !Expr !Expr

    -- | call out an effectful artifact, search only outer stack frames,
    -- if from an effectful procedure run
    | PerformExpr !AttrAddressor
    -- | call out an effectful artifact, always search full stack frames
    | BehaveExpr !AttrAddressor

    | AttrExpr !AttrAddr
    | IndexExpr { index'value :: !Expr
                , index'target :: !Expr
                }
    | CallExpr !Expr !ArgsPacker

    | InfixExpr !OpSymbol !Expr !Expr

    -- to support interpolation within expressions, with source form
    | ExprWithSrc !Expr ![SourceSeg]
    | IntplExpr !Expr
    | IntplSubs !EdhValue
  deriving (Eq, Show)

data SourceSeg = SrcSeg !Text | IntplSeg !Expr
  deriving (Eq, Show)

data Literal = SinkCtor
    | NilLiteral
    | DecLiteral !Decimal
    | BoolLiteral !Bool
    | StringLiteral !Text
    | TypeLiteral !EdhTypeValue
  deriving (Eq, Show)
instance Hashable Literal where
  hashWithSalt s SinkCtor          = hashWithSalt s (-1 :: Int)
  hashWithSalt s NilLiteral        = hashWithSalt s (0 :: Int)
  hashWithSalt s (DecLiteral    x) = hashWithSalt s x
  hashWithSalt s (BoolLiteral   x) = hashWithSalt s x
  hashWithSalt s (StringLiteral x) = hashWithSalt s x
  hashWithSalt s (TypeLiteral   x) = hashWithSalt s x


-- | the type for the value of type of a value
data EdhTypeValue = TypeType
    -- nil has no type, its type if you really ask, is nil
    | DecimalType
    | BoolType
    | StringType
    | BlobType
    | SymbolType
    | ObjectType
    | DictType
    | ListType
    | PairType
    | ArgsPackType
    | BlockType
    | HostClassType
    | HostMethodType
    | HostOperType
    | HostGenrType
    | IntrinsicType
    | ClassType
    | MethodType
    | OperatorType
    | GeneratorType
    | InterpreterType
    | ProducerType
    | DescriptorType
    | BreakType
    | ContinueType
    | CaseCloseType
    | CaseOtherType
    | FallthroughType
    | RethrowType
    | YieldType
    | ReturnType
    | DefaultType
    | SinkType
    | ExprType
  deriving (Enum, Eq, Ord, Show)
instance Hashable EdhTypeValue where
  hashWithSalt s t = hashWithSalt s $ fromEnum t

edhTypeNameOf :: EdhValue -> String
edhTypeNameOf EdhNil                   = "nil"
edhTypeNameOf (EdhNamedValue n EdhNil) = T.unpack n
edhTypeNameOf (EdhNamedValue n v) =
  T.unpack n <> " := " <> show (edhTypeNameOf v)
edhTypeNameOf v = show $ edhTypeOf v

-- | Get the type tag of an value
--
-- Passing in a `nil` value will hit bottom (crash the process) here,
-- use `edhTypeNameOf` if all you want is a type name shown to user.
edhTypeOf :: EdhValue -> EdhTypeValue

-- it's a taboo to get the type of a nil, either named or not
edhTypeOf EdhNil                   = undefined
edhTypeOf (EdhNamedValue _ EdhNil) = undefined

edhTypeOf EdhType{}                = TypeType

edhTypeOf EdhDecimal{}             = DecimalType
edhTypeOf EdhBool{}                = BoolType
edhTypeOf EdhBlob{}                = BlobType
edhTypeOf EdhString{}              = StringType
edhTypeOf EdhSymbol{}              = SymbolType
edhTypeOf EdhObject{}              = ObjectType
edhTypeOf EdhDict{}                = DictType
edhTypeOf EdhList{}                = ListType
edhTypeOf EdhPair{}                = PairType
edhTypeOf EdhArgsPack{}            = ArgsPackType

edhTypeOf EdhIntrOp{}              = IntrinsicType
edhTypeOf (EdhClass (ProcDefi _ _ _ (ProcDecl _ _ pb))) = case pb of
  Left  _ -> ClassType
  Right _ -> HostClassType
edhTypeOf (EdhMethod (ProcDefi _ _ _ (ProcDecl _ _ pb))) = case pb of
  Left  _ -> MethodType
  Right _ -> HostMethodType
edhTypeOf (EdhOprtor _ _ (ProcDefi _ _ _ (ProcDecl _ _ pb))) = case pb of
  Left  _ -> OperatorType
  Right _ -> HostOperType
edhTypeOf (EdhGnrtor (ProcDefi _ _ _ (ProcDecl _ _ pb))) = case pb of
  Left  _ -> GeneratorType
  Right _ -> HostGenrType

edhTypeOf EdhDescriptor{}     = DescriptorType

edhTypeOf EdhIntrpr{}         = InterpreterType
edhTypeOf EdhPrducr{}         = ProducerType
edhTypeOf EdhBreak            = BreakType
edhTypeOf EdhContinue         = ContinueType
edhTypeOf EdhCaseClose{}      = CaseCloseType
edhTypeOf EdhCaseOther        = CaseOtherType
edhTypeOf EdhFallthrough      = FallthroughType
edhTypeOf EdhRethrow          = RethrowType
edhTypeOf EdhYield{}          = YieldType
edhTypeOf EdhReturn{}         = ReturnType
edhTypeOf EdhDefault{}        = DefaultType
edhTypeOf EdhSink{}           = SinkType
edhTypeOf (EdhNamedValue _ v) = edhTypeOf v
edhTypeOf EdhExpr{}           = ExprType


mkIntrinsicOp :: EdhWorld -> OpSymbol -> EdhIntrinsicOp -> STM EdhValue
mkIntrinsicOp !world !opSym !iop = do
  u <- unsafeIOToSTM newUnique
  Map.lookup opSym <$> readTMVar (worldOperators world) >>= \case
    Nothing ->
      throwSTM
        $ EdhError
            UsageError
            ("No precedence declared in the world for operator: " <> opSym)
        $ EdhCallContext "<edh>" []
    Just (preced, _) -> return $ EdhIntrOp preced $ IntrinOpDefi u opSym iop


mkHostProc
  :: Scope
  -> (ProcDefi -> EdhValue)
  -> Text
  -> EdhProcedure
  -> ArgsReceiver
  -> STM EdhValue
mkHostProc !scope !vc !nm !p !args = do
  u <- unsafeIOToSTM newUnique
  return $ vc ProcDefi
    { procedure'uniq = u
    , procedure'name = AttrByName nm
    , procedure'lexi = Just scope
    , procedure'decl = ProcDecl { procedure'addr = NamedAttr nm
                                , procedure'args = args
                                , procedure'body = Right p
                                }
    }

mkSymbolicHostProc
  :: Scope
  -> (ProcDefi -> EdhValue)
  -> Symbol
  -> EdhProcedure
  -> ArgsReceiver
  -> STM EdhValue
mkSymbolicHostProc !scope !vc !sym !p !args = do
  u <- unsafeIOToSTM newUnique
  return $ vc ProcDefi
    { procedure'uniq = u
    , procedure'name = AttrBySym sym
    , procedure'lexi = Just scope
    , procedure'decl = ProcDecl { procedure'addr = SymbolicAttr $ symbolName sym
                                , procedure'args = args
                                , procedure'body = Right p
                                }
    }


mkHostProperty
  :: Scope -> Text -> EdhProcedure -> Maybe EdhProcedure -> STM EdhValue
mkHostProperty !scope !nm !getterProc !maybeSetterProc = do
  getter <- do
    u <- unsafeIOToSTM newUnique
    return $ ProcDefi
      { procedure'uniq = u
      , procedure'name = AttrByName nm
      , procedure'lexi = Just scope
      , procedure'decl = ProcDecl { procedure'addr = NamedAttr nm
                                  , procedure'args = PackReceiver []
                                  , procedure'body = Right getterProc
                                  }
      }
  setter <- case maybeSetterProc of
    Nothing          -> return Nothing
    Just !setterProc -> do
      u <- unsafeIOToSTM newUnique
      return $ Just $ ProcDefi
        { procedure'uniq = u
        , procedure'name = AttrByName nm
        , procedure'lexi = Just scope
        , procedure'decl = ProcDecl
          { procedure'addr = NamedAttr nm
          , procedure'args = PackReceiver
                               [optionalArg "newValue" $ LitExpr NilLiteral]
          , procedure'body = Right setterProc
          }
        }
  return $ EdhDescriptor getter setter


type EdhHostCtor
  =  EdhProgState
  -- | ctor args, if __init__() is provided, will go there too
  -> ArgsPack
  -- | exit for in-band data to be written to entity store
  -> (Dynamic -> STM ())
  -> STM ()

-- | Make a host class with a 'EdhHostCtor' and custom entity manipulater
--
-- The entity manipulater is responsible to manage all kinds of instance
-- attributes, including methods and mutable ones.
--
-- Note that even as an object method procedure, a host procedure's contextual
-- `this` instance is the enclosed this object at the time it's defined (i.e.
-- `this` in the scope passed to 'mkHostProc' that produced the host procedure,
-- which is normally a host module), so such host methods normally operate
-- against `that` instance's in-band storage.
--
-- `that` object is always the final instance down to the inheritance
-- hierarchy, will be an Edh object if it extended such a host class instance,
-- and will definitely not carrying the entity store produced by the
-- 'EdhHostCtor' here. Use 'mkExtHostClass' to create host methods resolving
-- the host class instance against `that`, to operate properly.
--
-- See: 'withThatEntity'
mkHostClass
  :: Scope -- ^ outer lexical scope
  -> Text  -- ^ class name
  -> EdhHostCtor -- ^ instance constructor
  -> EntityManipulater -- ^ custom entity storage manipulater
  -> STM EdhValue
mkHostClass !scope !nm !hc !esm = do
  classUniq <- unsafeIOToSTM newUnique
  let !cls = ProcDefi
        { procedure'uniq = classUniq
        , procedure'name = AttrByName nm
        , procedure'lexi = Just scope
        , procedure'decl = ProcDecl { procedure'addr = NamedAttr nm
                                    , procedure'args = PackReceiver []
                                    , procedure'body = Right ctor
                                    }
        }
      ctor :: EdhProcedure
      ctor !apk !exit = ask >>= \ !pgs -> contEdhSTM $ hc pgs apk $ \ !esd ->
        do
          !ent     <- createSideEntity esm esd
          !newThis <- viewAsEdhObject ent cls []
          exitEdhSTM pgs exit $ EdhObject newThis
  return $ EdhClass cls

-- | Make an extensible (by Edh objects) host class with a 'EdhHostCtor' and
-- custom entity manipulater
--
-- When a host object carries some method operating against `that` instance,
-- it won't be properly extended by other Edh objects, because `that` will 
-- refer to that final Edh instance instead. Here the entity manipulater 
-- creator is passed a unique identifier of the host class to be created, so
-- you should let your host methods to 'resolveEdhInstance' of this class id
-- agsinst `that` instance, to obtain the correct instance with entity store
-- created by your 'EdhHostCtor' passed here.
--
-- See: 'withEntityOfClass'
mkExtHostClass
  :: Scope -- ^ outer lexical scope
  -> Text  -- ^ class name
  -> EdhHostCtor -- ^ instance constructor
  -- | custom entity storage manipulater creator
  -> (Unique -> STM EntityManipulater)
  -> STM EdhValue
mkExtHostClass !scope !nm !hc !esmCtor = do
  classUniq <- unsafeIOToSTM newUnique
  esm       <- esmCtor classUniq
  let !cls = ProcDefi
        { procedure'uniq = classUniq
        , procedure'name = AttrByName nm
        , procedure'lexi = Just scope
        , procedure'decl = ProcDecl { procedure'addr = NamedAttr nm
                                    , procedure'args = PackReceiver []
                                    , procedure'body = Right ctor
                                    }
        }
      ctor :: EdhProcedure
      ctor !apk !exit = ask >>= \ !pgs -> contEdhSTM $ hc pgs apk $ \ !esd ->
        do
          !ent     <- createSideEntity esm esd
          !newThis <- viewAsEdhObject ent cls []
          exitEdhSTM pgs exit $ EdhObject newThis
  return $ EdhClass cls


data EdhIndex = EdhIndex !Int | EdhAny | EdhAll | EdhSlice {
    edh'slice'start :: !(Maybe Int)
  , edh'slice'stop :: !(Maybe Int)
  , edh'slice'step :: !(Maybe Int)
  } deriving (Eq)

