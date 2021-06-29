-- | core language functionalities
module Language.Edh.CoreLang where

-- import           Debug.Trace

import Control.Concurrent.STM (STM, readTVar, writeTVar)
import Data.Either (partitionEithers)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Language.Edh.IOPD
import Language.Edh.RtTypes
import Prelude

prepareMagicStore ::
  AttrKey ->
  EntityStore ->
  (EntityStore -> STM Object) ->
  STM EntityStore
prepareMagicStore !magicName !tgtEnt !wrapAsObj =
  iopdLookup magicName tgtEnt >>= \case
    -- todo warn if of wrong type
    Just (EdhObject !obj) -> case edh'obj'store obj of
      HashStore !es -> return es
      _ -> implantNew
    _ -> implantNew
  where
    implantNew = do
      !es <- iopdEmpty
      !wrapper <- wrapAsObj es
      iopdInsert magicName (EdhObject wrapper) tgtEnt
      return es

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

edhEffectDefaultsMagicName :: Text
edhEffectDefaultsMagicName = "__effect_defaults__"

resolveEffectfulAttr ::
  EdhThreadState ->
  AttrKey ->
  [EdhCallFrame] ->
  STM (Maybe (EdhValue, [EdhCallFrame]))
resolveEffectfulAttr ets !k = resolve
  where
    resolve [] =
      iopdLookup
        (AttrByName edhEffectDefaultsMagicName)
        (edh'scope'entity $ contextScope $ edh'context ets)
        >>= \case
          Nothing -> return Nothing
          Just (EdhObject !effsObj) -> case edh'obj'store effsObj of
            HashStore !esEffDefs ->
              iopdLookup k esEffDefs >>= \case
                Nothing -> return Nothing
                Just !val -> return $ Just (val, [])
            -- todo crash in these cases?
            --      warning may be more proper but in what way?
            _ -> return Nothing
          _ -> return Nothing
    resolve (EdhCallFrame scope _ _ : rest) =
      iopdLookup (AttrByName edhEffectsMagicName) (edh'scope'entity scope)
        >>= \case
          Nothing -> resolve rest
          Just (EdhObject !effsObj) -> case edh'obj'store effsObj of
            HashStore !esEffs ->
              iopdLookup k esEffs >>= \case
                Just !val -> case val of
                  EdhProcedure !callable _origEffOuterStack ->
                    return $
                      Just (EdhProcedure callable (Just rest), rest)
                  EdhBoundProc !callable !this !that _origEffOuterStack ->
                    return $
                      Just (EdhBoundProc callable this that (Just rest), rest)
                  _ -> return $ Just (val, rest)
                Nothing -> resolve rest
            -- todo crash in these cases?
            --      warning may be more proper but in what way?
            _ -> resolve rest
          _ -> resolve rest
{-# INLINE resolveEffectfulAttr #-}

resolveEffectfulDefault ::
  EdhThreadState ->
  AttrKey ->
  [EdhCallFrame] ->
  STM (Maybe (EdhValue, [EdhCallFrame]))
resolveEffectfulDefault _ets !k = resolve
  where
    resolve [] = return Nothing
    resolve (EdhCallFrame scope _ _ : rest) =
      iopdLookup
        (AttrByName edhEffectDefaultsMagicName)
        (edh'scope'entity scope)
        >>= \case
          Nothing -> resolve rest
          Just (EdhObject !effsObj) -> case edh'obj'store effsObj of
            HashStore !esEffs ->
              iopdLookup k esEffs >>= \case
                Just !val -> case val of
                  EdhProcedure !callable _origEffOuterStack ->
                    return $
                      Just (EdhProcedure callable (Just rest), rest)
                  EdhBoundProc !callable !this !that _origEffOuterStack ->
                    return $
                      Just (EdhBoundProc callable this that (Just rest), rest)
                  _ -> return $ Just (val, rest)
                Nothing -> resolve rest
            -- todo crash in these cases?
            --      warning may be more proper but in what way?
            _ -> resolve rest
          _ -> resolve rest
{-# INLINE resolveEffectfulDefault #-}

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
  {- HLINT ignore "Redundant <$>" -}
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
        return $
          Left $
            "class expected but given an object of "
              <> objClassName c

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
              | h' == h =
                checkTail rest $ if null t' then neTails else t' : neTails
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
lookupEdhObjAttr !obj !key =
  lookupEdhSelfAttr obj key >>= \case
    EdhNil -> case edh'obj'store obj of
      ClassStore !cls -> readTVar (edh'class'mro cls) >>= searchSuperClasses
      _ -> lookupEdhSuperAttr obj key
    !val -> return (obj, val)
  where
    searchSuperClasses :: [Object] -> STM (Object, EdhValue)
    searchSuperClasses !supers = lookupFromSupers supers
      where
        lookupFromSupers [] = return (obj, EdhNil)
        lookupFromSupers (super : rest) =
          lookupEdhSelfAttr super key >>= \ !val -> case val of
            EdhNil -> lookupFromSupers rest
            _ -> return (super, val)
{-# INLINE lookupEdhObjAttr #-}

lookupEdhSuperAttr :: Object -> AttrKey -> STM (Object, EdhValue)
lookupEdhSuperAttr !obj !key = readTVar (edh'obj'supers obj) >>= searchSupers
  where
    searchSupers :: [Object] -> STM (Object, EdhValue)
    searchSupers !supers = lookupFromSupers supers
      where
        lookupFromSupers [] = return (obj, EdhNil)
        lookupFromSupers (super : rest) =
          lookupEdhSelfAttr super key >>= \ !val -> case val of
            EdhNil -> lookupFromSupers rest
            _ -> return (super, val)
{-# INLINE lookupEdhSuperAttr #-}

lookupEdhSelfAttr :: Object -> AttrKey -> STM EdhValue
lookupEdhSelfAttr !obj !key = case edh'obj'store obj of
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
      if clsObj == obj
        then return EdhNil -- reached ultimate meta class of the world
        else case edh'obj'store clsObj of
          ClassStore !cls ->
            iopdLookup key (edh'class'store cls) >>= \case
              Just !v -> return v
              Nothing -> return EdhNil -- don't resort to meta class here
          _ -> return EdhNil -- todo should complain loudly here?
      where
        !clsObj = edh'obj'class obj
{-# INLINE lookupEdhSelfAttr #-}

lookupEdhSelfMagic :: Object -> AttrKey -> STM EdhValue
lookupEdhSelfMagic !obj !key = case edh'obj'store obj of
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
        !clsObj = edh'obj'class obj
{-# INLINE lookupEdhSelfMagic #-}

lookupEdhObjMagic :: Object -> AttrKey -> STM (Object, EdhValue)
lookupEdhObjMagic !obj !key =
  (obj :) <$> readTVar (edh'obj'supers obj) >>= searchMagic
  where
    searchMagic [] = return (obj, EdhNil)
    searchMagic (o : rest) =
      lookupEdhSelfMagic o key >>= \case
        EdhNil -> searchMagic rest
        !art -> return (o, art)
{-# INLINE lookupEdhObjMagic #-}

-- * import/export

normalizeImportSpec :: Text -> Text
normalizeImportSpec = withoutLeadingSlash . withoutTrailingSlash
  where
    withoutLeadingSlash spec = fromMaybe spec $ T.stripPrefix "/" spec
    withoutTrailingSlash spec = fromMaybe spec $ T.stripSuffix "/" spec
{-# INLINE normalizeImportSpec #-}

edhExportsMagicName :: Text
edhExportsMagicName = "__exports__"
