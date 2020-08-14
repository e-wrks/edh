
-- | core language functionalities
module Language.Edh.Details.CoreLang where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import           Data.Text                      ( Text )

import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes


-- * Edh lexical attribute resolution


lookupEdhCtxAttr :: EdhThreadState -> Scope -> AttrKey -> STM EdhValue
lookupEdhCtxAttr ets !fromScope !key =
  resolveEdhCtxAttr ets fromScope key >>= \case
    Nothing        -> return EdhNil
    Just (!val, _) -> return val
{-# INLINE lookupEdhCtxAttr #-}

resolveEdhCtxAttr
  :: EdhThreadState -> Scope -> AttrKey -> STM (Maybe (EdhValue, Scope))
resolveEdhCtxAttr _ets !fromScope !key = resolveLexicalAttr (Just fromScope)
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

resolveEffectfulAttr
  :: EdhThreadState -> [Scope] -> EdhValue -> STM (Maybe (EdhValue, [Scope]))
resolveEffectfulAttr _ [] _ = return Nothing
resolveEffectfulAttr ets (scope : rest) !key =
  iopdLookup (AttrByName edhEffectsMagicName) (edh'scope'entity scope) >>= \case
    Nothing                    -> resolveEffectfulAttr ets rest key
    Just (EdhDict (Dict _ !d)) -> iopdLookup key d >>= \case
      Just val -> return $ Just (val, rest)
      Nothing  -> resolveEffectfulAttr ets rest key
-- todo crash in this case? warning may be more proper but in what way?
    _ -> resolveEffectfulAttr ets rest key
{-# INLINE resolveEffectfulAttr #-}


-- * Edh inheritance resolution


resolveEdhInstance :: EdhThreadState -> Object -> Object -> STM (Maybe Object)
resolveEdhInstance _ets !classObj !that = if classObj == edh'obj'class that
  then return $ Just that
  else readTVar (edh'obj'supers that) >>= matchSupers
 where
  matchSupers []             = return Nothing
  matchSupers (super : rest) = if classObj == edh'obj'class super
    then return $ Just super
    else matchSupers rest
{-# INLINE resolveEdhInstance #-}


-- * Edh object attribute resolution


lookupEdhObjAttr
  :: EdhThreadState -> Object -> AttrKey -> STM (Object, EdhValue)
lookupEdhObjAttr ets !this !key = _lookupFromSelf ets this key >>= \case
  EdhNil -> lookupEdhSuperAttr ets this key
  !val   -> return (this, val)
{-# INLINE lookupEdhObjAttr #-}

lookupEdhSuperAttr
  :: EdhThreadState -> Object -> AttrKey -> STM (Object, EdhValue)
lookupEdhSuperAttr ets !this !key =
  readTVar (edh'obj'supers this) >>= _lookupFromSupersOf ets this key
{-# INLINE lookupEdhSuperAttr #-}


_lookupFromSelf :: EdhThreadState -> Object -> AttrKey -> STM EdhValue
_lookupFromSelf _ets !this !key = case edh'obj'store this of
  HostStore{}   -> lookupFromClassOf this
  HashStore !es -> iopdLookup key es >>= \case
    Just !v -> return v
    Nothing -> lookupFromClassOf this
  ClassStore (Class _ !cs _) -> iopdLookup key cs >>= \case
    Just !v -> return v
    Nothing -> lookupFromClassOf this
 where
  lookupFromClassOf !obj = if clsObj == obj
    then return EdhNil -- reached ultimate meta class of the world
    else case edh'obj'store clsObj of
      ClassStore (Class _ !cs _) -> iopdLookup key cs >>= \case
        Just !v -> return v
        Nothing -> lookupFromClassOf clsObj
      _ -> lookupFromClassOf clsObj
    where !clsObj = edh'obj'class obj

_lookupFromSupersOf
  :: EdhThreadState -> Object -> AttrKey -> [Object] -> STM (Object, EdhValue)
_lookupFromSupersOf ets !this !key !supers = lookupFromSupers supers
 where
  lookupFromSupers [] = return (this, EdhNil)
  lookupFromSupers (super : rest) =
    _lookupFromSelf ets super key >>= \ !val -> case val of
      EdhNil -> lookupFromSupers rest
      _      -> return (super, val)

