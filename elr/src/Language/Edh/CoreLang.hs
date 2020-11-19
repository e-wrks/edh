-- | core language functionalities
module Language.Edh.CoreLang where

-- import           Debug.Trace

import Control.Concurrent.STM (STM, readTVar, writeTVar)
import Data.Either (partitionEithers)
import Data.Text (Text)
import qualified Data.Text as T
import Language.Edh.IOPD (iopdLookup)
import Language.Edh.RtTypes
  ( AttrKey (AttrByName),
    Class (Class, edh'class'mro, edh'class'store),
    Dict (Dict),
    EdhCallFrame (EdhCallFrame),
    EdhValue (EdhBoundProc, EdhDict, EdhNil, EdhProcedure),
    Object (edh'obj'class, edh'obj'store, edh'obj'supers),
    ObjectStore (ClassStore, HashStore, HostStore),
    Scope (edh'scope'entity),
    objClassName,
    outerScopeOf,
  )
import Prelude

-- * Edh lexical attribute resolution

lookupEdhCtxAttr :: Scope -> AttrKey -> STM EdhValue
lookupEdhCtxAttr !fromScope !key =
  resolveEdhCtxAttr fromScope key >>= \case
    Nothing -> return EdhNil
    Just (!val, _) -> return val
{-# INLINE lookupEdhCtxAttr #-}

resolveEdhCtxAttr :: Scope -> AttrKey -> STM (Maybe (EdhValue, Scope))
resolveEdhCtxAttr !fromScope !key = resolveLexicalAttr (Just fromScope)
  where
    resolveLexicalAttr Nothing = return Nothing
    resolveLexicalAttr (Just !scope) =
      iopdLookup key (edh'scope'entity scope) >>= \case
        Nothing -> resolveLexicalAttr (outerScopeOf scope)
        Just !val -> return $ Just (val, scope)
{-# INLINE resolveEdhCtxAttr #-}

-- * Edh effectful attribute resolution

edhEffectsMagicName :: Text
edhEffectsMagicName = "__effects__"

resolveEffectfulAttr ::
  [EdhCallFrame] -> EdhValue -> STM (Maybe (EdhValue, [EdhCallFrame]))
resolveEffectfulAttr [] _ = return Nothing
resolveEffectfulAttr (EdhCallFrame scope _ _ : rest) !key =
  iopdLookup (AttrByName edhEffectsMagicName) (edh'scope'entity scope) >>= \case
    Nothing -> resolveEffectfulAttr rest key
    Just (EdhDict (Dict _ !d)) ->
      iopdLookup key d >>= \case
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
      Left !mroInvalid -> return mroInvalid
      Right !selfL -> do
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
    merge [] !result = return $ reverse result
    merge lists result = do
      (goodHead, lists') <- pickHead lists
      merge lists' (goodHead : result)
      where
        pickHead :: [[Object]] -> Either Text (Object, [[Object]])
        pickHead [] = error "bug: empty list of lists passed to pickHead"
        pickHead (l2t : lsBacklog) = tryHeads l2t lsBacklog []

        tryHeads ::
          [Object] ->
          [[Object]] ->
          [[Object]] ->
          Either Text (Object, [[Object]])
        tryHeads [] _ _ = error "bug: empty list to try"
        tryHeads l2t@(h : t) lsBacklog lsTried =
          let (nowhereTail, neTails) =
                checkTail (lsBacklog ++ lsTried) [t | not (null t)]
           in if nowhereTail
                then return (h, neTails)
                else case lsBacklog of
                  [] -> Left "no C3 linearization exists"
                  n2t : lsBacklog' -> tryHeads n2t lsBacklog' (l2t : lsTried)
          where
            checkTail :: [[Object]] -> [[Object]] -> (Bool, [[Object]])
            checkTail [] neTails = (True, neTails)
            checkTail ([] : _) _ = error "bug: empty list in rest of the lists"
            checkTail (l2c@(h' : t') : rest) neTails
              | h' == h = checkTail rest $ if null t' then neTails else t' : neTails
              | h `elem` t' = (False, [])
              | otherwise = checkTail rest (l2c : neTails)

resolveEdhInstance :: Object -> Object -> STM (Maybe Object)
resolveEdhInstance !classObj !that =
  if classObj == edh'obj'class that
    then return $ Just that
    else readTVar (edh'obj'supers that) >>= matchSupers
  where
    matchSupers [] = return Nothing
    matchSupers (super : rest) =
      if classObj == edh'obj'class super
        then return $ Just super
        else matchSupers rest
{-# INLINE resolveEdhInstance #-}

-- * Edh object attribute resolution

lookupEdhObjAttr :: Object -> AttrKey -> STM (Object, EdhValue)
lookupEdhObjAttr !this !key =
  lookupEdhSelfAttr this key >>= \case
    EdhNil -> case edh'obj'store this of
      ClassStore !cls -> readTVar (edh'class'mro cls) >>= searchSuperClasses
      _ -> lookupEdhSuperAttr this key
    !val -> return (this, val)
  where
    searchSuperClasses :: [Object] -> STM (Object, EdhValue)
    searchSuperClasses !supers = lookupFromSupers supers
      where
        lookupFromSupers [] = return (this, EdhNil)
        lookupFromSupers (super : rest) =
          lookupEdhSelfAttr super key >>= \ !val -> case val of
            EdhNil -> lookupFromSupers rest
            _ -> return (super, val)
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
            _ -> return (super, val)
{-# INLINE lookupEdhSuperAttr #-}

lookupEdhSelfAttr :: Object -> AttrKey -> STM EdhValue
lookupEdhSelfAttr !this !key = case edh'obj'store this of
  HostStore {} -> lookupFromClass
  HashStore !es ->
    iopdLookup key es >>= \case
      Just !v -> return v
      Nothing -> lookupFromClass
  ClassStore !cls ->
    iopdLookup key (edh'class'store cls) >>= \case
      Just !v -> return v
      Nothing -> lookupFromClass
  where
    lookupFromClass =
      if clsObj == this
        then return EdhNil -- reached ultimate meta class of the world
        else case edh'obj'store clsObj of
          ClassStore !cls ->
            iopdLookup key (edh'class'store cls) >>= \case
              Just !v -> return v
              Nothing -> return EdhNil -- don't resort to meta class here
          _ -> return EdhNil -- todo should complain loudly here?
      where
        !clsObj = edh'obj'class this
{-# INLINE lookupEdhSelfAttr #-}

lookupEdhSelfMagic :: Object -> AttrKey -> STM EdhValue
lookupEdhSelfMagic !this !key = case edh'obj'store this of
  HostStore {} ->
    -- a host object can only have magic attributes on its class
    lookupFromClass
  HashStore !es ->
    -- unlike in Python, here we honor magic attributes from
    -- an object itself
    iopdLookup key es >>= \case
      Just !v -> return v
      Nothing -> lookupFromClass
  ClassStore {} ->
    -- magic attributes on a class are assumed for its instances,
    -- not for itself
    lookupFromClass
  where
    lookupFromClass = case edh'obj'store clsObj of
      ClassStore !cls ->
        iopdLookup key (edh'class'store cls) >>= \case
          Just !v -> return v
          Nothing -> return EdhNil -- don't resort to meta class here
      _ -> return EdhNil -- todo should complain loudly here?
      where
        !clsObj = edh'obj'class this
{-# INLINE lookupEdhSelfMagic #-}

lookupEdhObjMagic :: Object -> AttrKey -> STM (Object, EdhValue)
lookupEdhObjMagic !this !key =
  (this :) <$> readTVar (edh'obj'supers this) >>= searchMagic
  where
    searchMagic [] = return (this, EdhNil)
    searchMagic (obj : rest) =
      lookupEdhSelfMagic obj key >>= \case
        EdhNil -> searchMagic rest
        !art -> return (obj, art)
{-# INLINE lookupEdhObjMagic #-}

-- * import/export

edhExportsMagicName :: Text
edhExportsMagicName = "__exports__"
