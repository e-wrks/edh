
-- | core language functionalities
module Language.Edh.Details.CoreLang where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad
import           Control.Concurrent.STM

import           Data.Either
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Unique
import           Data.Dynamic

import           Text.Megaparsec

import           Language.Edh.Control
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes


-- * Edh lexical attribute resolution


lookupEdhCtxAttr :: Scope -> AttrKey -> STM EdhValue
lookupEdhCtxAttr !fromScope !key = resolveEdhCtxAttr fromScope key >>= \case
  Nothing        -> return EdhNil
  Just (!val, _) -> return val
{-# INLINE lookupEdhCtxAttr #-}

resolveEdhCtxAttr :: Scope -> AttrKey -> STM (Maybe (EdhValue, Scope))
resolveEdhCtxAttr !fromScope !key = resolveLexicalAttr (Just fromScope)
 where
  resolveLexicalAttr Nothing = return Nothing
  resolveLexicalAttr (Just !scope) =
    iopdLookup key (edh'scope'entity scope) >>= \case
      Nothing   -> resolveLexicalAttr (outerScopeOf scope)
      Just !val -> return $ Just (val, scope)
{-# INLINE resolveEdhCtxAttr #-}


-- * Edh effectful attribute resolution


edhEffectsMagicName :: Text
edhEffectsMagicName = "__effects__"

resolveEffectfulAttr :: [Scope] -> EdhValue -> STM (Maybe (EdhValue, [Scope]))
resolveEffectfulAttr [] _ = return Nothing
resolveEffectfulAttr (scope : rest) !key =
  iopdLookup (AttrByName edhEffectsMagicName) (edh'scope'entity scope) >>= \case
    Nothing                    -> resolveEffectfulAttr rest key
    Just (EdhDict (Dict _ !d)) -> iopdLookup key d >>= \case
      Just !val -> case val of
        EdhProcedure !callable _origEffOuterStack ->
          return $ Just (EdhProcedure callable (Just rest), rest)
        EdhBoundProc !callable !this !that _origEffOuterStack ->
          return $ Just (EdhBoundProc callable this that (Just rest), rest)
        _ -> return $ Just (val, rest)
      Nothing -> resolveEffectfulAttr rest key
-- todo crash in this case? warning may be more proper but in what way?
    _ -> resolveEffectfulAttr rest key
{-# INLINE resolveEffectfulAttr #-}


-- * Edh inheritance resolution


-- | Calculate the C3 linearization of the super classes and fill into the
-- class' mro list.
--
-- Note we don't store self in the mro list here.
--
-- For the algorithm see:
--   https://en.wikipedia.org/wiki/C3_linearization
fillClassMRO :: Class -> [Object] -> STM Text
fillClassMRO _ [] = return ""
fillClassMRO !cls !superClasses =

  partitionEithers <$> sequence (l <$> superClasses) >>= \case
    ([], !superLs) -> case merge (superLs ++ [superClasses]) [] of
      Left  !mroInvalid -> return mroInvalid
      Right !selfL      -> do
        writeTVar (edh'class'mro cls) selfL
        return ""
    (errs, _) -> return $ T.intercalate "; " errs

 where

  l :: Object -> STM (Either Text [Object])
  l !c = case edh'obj'store c of
    ClassStore (Class _ _ _ !mro) -> Right . (c :) <$> readTVar mro
    _ ->
      return $ Left $ "class expected but given an object of " <> objClassName c

  merge :: [[Object]] -> [Object] -> Either Text [Object]
  merge []    !result = return $ reverse result
  merge lists result  = do
    (goodHead, lists') <- pickHead lists
    merge lists' (goodHead : result)

   where

    pickHead :: [[Object]] -> Either Text (Object, [[Object]])
    pickHead [] = error "bug: empty list of lists passed to pickHead"
    pickHead (l2t : lsBacklog) = tryHeads l2t lsBacklog []

    tryHeads
      :: [Object]
      -> [[Object]]
      -> [[Object]]
      -> Either Text (Object, [[Object]])
    tryHeads [] _ _ = error "bug: empty list to try"
    tryHeads l2t@(h : t) lsBacklog lsTried =
      let (nowhereTail, neTails) =
              checkTail (lsBacklog ++ lsTried) [ t | not (null t) ]
      in  if nowhereTail
            then return (h, neTails)
            else case lsBacklog of
              []               -> Left "no C3 linearization exists"
              n2t : lsBacklog' -> tryHeads n2t lsBacklog' (l2t : lsTried)
     where
      checkTail :: [[Object]] -> [[Object]] -> (Bool, [[Object]])
      checkTail []       neTails = (True, neTails)
      checkTail ([] : _) _       = error "bug: empty list in rest of the lists"
      checkTail (l2c@(h' : t') : rest) neTails
        | h' == h = checkTail rest $ if null t' then neTails else t' : neTails
        | h `elem` t' = (False, [])
        | otherwise = checkTail rest (l2c : neTails)


mkHostClass
  :: Scope
  -> AttrName
  -> EdhObjectAllocator
  -> EntityStore
  -> [Object]
  -> STM Object
mkHostClass !scope !className !allocator !classStore !superClasses = do
  !idCls  <- unsafeIOToSTM newUnique
  !ssCls  <- newTVar superClasses
  !mroCls <- newTVar []
  let !clsProc = ProcDefi idCls (AttrByName className) scope
        $ ProcDecl (NamedAttr className) (PackReceiver []) (Right fakeHostProc)
      !cls    = Class clsProc classStore allocator mroCls
      !clsObj = Object idCls (ClassStore cls) metaClassObj ssCls
  !mroInvalid <- fillClassMRO cls superClasses
  unless (T.null mroInvalid)
    $ throwSTM
    $ EdhError UsageError mroInvalid (toDyn nil)
    $ EdhCallContext "<mkHostClass>" []
  return clsObj
 where
  fakeHostProc :: EdhHostProc
  fakeHostProc _ !exit = exitEdhTx exit nil

  !metaClassObj =
    edh'obj'class $ edh'obj'class $ edh'scope'this $ rootScopeOf scope

mkHostClass'
  :: Scope
  -> AttrName
  -> EdhObjectAllocator
  -> [Object]
  -> (Scope -> STM ())
  -> STM Object
mkHostClass' !scope !className !allocator !superClasses !storeMod = do
  !classStore <- iopdEmpty
  !idCls      <- unsafeIOToSTM newUnique
  !ssCls      <- newTVar superClasses
  !mroCls     <- newTVar []
  let !clsProc = ProcDefi idCls (AttrByName className) scope
        $ ProcDecl (NamedAttr className) (PackReceiver []) (Right fakeHostProc)
      !cls      = Class clsProc classStore allocator mroCls
      !clsObj   = Object idCls (ClassStore cls) metaClassObj ssCls
      !clsScope = scope { edh'scope'entity  = classStore
                        , edh'scope'this    = clsObj
                        , edh'scope'that    = clsObj
                        , edh'excpt'hndlr   = defaultEdhExcptHndlr
                        , edh'scope'proc    = clsProc
                        , edh'scope'caller  = clsCreStmt
                        , edh'effects'stack = []
                        }
  storeMod clsScope
  !mroInvalid <- fillClassMRO cls superClasses
  unless (T.null mroInvalid)
    $ throwSTM
    $ EdhError UsageError mroInvalid (toDyn nil)
    $ EdhCallContext "<mkHostClass>" []
  return clsObj
 where
  fakeHostProc :: EdhHostProc
  fakeHostProc _ !exit = exitEdhTx exit nil

  !metaClassObj =
    edh'obj'class $ edh'obj'class $ edh'scope'this $ rootScopeOf scope

  clsCreStmt :: StmtSrc
  clsCreStmt = StmtSrc
    ( SourcePos { sourceName   = "<host-class-creation>"
                , sourceLine   = mkPos 1
                , sourceColumn = mkPos 1
                }
    , VoidStmt
    )


resolveEdhInstance :: Object -> Object -> STM (Maybe Object)
resolveEdhInstance !classObj !that = if classObj == edh'obj'class that
  then return $ Just that
  else readTVar (edh'obj'supers that) >>= matchSupers
 where
  matchSupers []             = return Nothing
  matchSupers (super : rest) = if classObj == edh'obj'class super
    then return $ Just super
    else matchSupers rest
{-# INLINE resolveEdhInstance #-}


-- * Edh object attribute resolution


lookupEdhObjAttr :: Object -> AttrKey -> STM (Object, EdhValue)
lookupEdhObjAttr !this !key = lookupEdhSelfAttr this key >>= \case
  EdhNil -> lookupEdhSuperAttr this key
  !val   -> return (this, val)
{-# INLINE lookupEdhObjAttr #-}

lookupEdhSuperAttr :: Object -> AttrKey -> STM (Object, EdhValue)
lookupEdhSuperAttr !this !key = readTVar (edh'obj'supers this) >>= searchSupers
 where
  searchSupers :: [Object] -> STM (Object, EdhValue)
  searchSupers !supers = lookupFromSupers supers
   where
    lookupFromSupers [] = return (this, EdhNil)
    lookupFromSupers (super : rest) =
      lookupEdhSelfAttr super key >>= \ !val -> case val of
        EdhNil -> lookupFromSupers rest
        _      -> return (super, val)
{-# INLINE lookupEdhSuperAttr #-}

lookupEdhSelfAttr :: Object -> AttrKey -> STM EdhValue
lookupEdhSelfAttr !this !key = case edh'obj'store this of
  HostStore{}   -> lookupFromClassOf this
  HashStore !es -> iopdLookup key es >>= \case
    Just !v -> return v
    Nothing -> lookupFromClassOf this
  ClassStore !cls -> iopdLookup key (edh'class'store cls) >>= \case
    Just !v -> return v
    Nothing -> lookupFromClassOf this
 where
  lookupFromClassOf !obj = if clsObj == obj
    then return EdhNil -- reached ultimate meta class of the world
    else case edh'obj'store clsObj of
      ClassStore !cls -> iopdLookup key (edh'class'store cls) >>= \case
        Just !v -> return v
        Nothing -> return EdhNil -- don't resort to meta class here
      _ -> return EdhNil -- todo should complain loudly here?
    where !clsObj = edh'obj'class obj
{-# INLINE lookupEdhSelfAttr #-}


-- * Edh object manipulation


-- Clone `that` object with one of its super object (i.e. `this`) mutated
-- to bear the new object stroage
edhMutCloneObj :: Object -> Object -> ObjectStore -> STM Object
edhMutCloneObj !fromThis !fromThat !newStore = do
  !oidNewThis <- unsafeIOToSTM newUnique
  let !newThis =
        fromThis { edh'obj'ident = oidNewThis, edh'obj'store = newStore }
  if fromThis == fromThat
    then return newThis
    else do
      let

        substThis :: [Object] -> [Object] -> [Object]
        substThis [] !supersNew = reverse supersNew
        substThis (super : rest) !supersNew =
          substThis rest
            $ (if super == fromThis then newThis else super)
            : supersNew

      !supers     <- readTVar $ edh'obj'supers fromThat
      !oidNewThat <- unsafeIOToSTM newUnique
      !supersNew  <- newTVar $! substThis supers []
      return
        $ fromThat { edh'obj'ident = oidNewThat, edh'obj'supers = supersNew }

-- Clone `that` object with one of its super object (i.e. `this`) mutated
-- to bear the new host storage data
-- 
-- todo maybe check new storage data type matches the old one?
edhCloneHostObj :: Object -> Object -> Dynamic -> STM Object
edhCloneHostObj !fromThis !fromThat !newData =
  HostStore <$> newTVar newData >>= edhMutCloneObj fromThis fromThat


-- * import/export


edhExportsMagicName :: Text
edhExportsMagicName = "__exports__"
