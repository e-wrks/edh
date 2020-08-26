
-- | core language functionalities
module Language.Edh.Details.CoreLang where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import           Data.Unique

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

