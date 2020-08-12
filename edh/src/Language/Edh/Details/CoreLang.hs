
-- | core language functionalities
module Language.Edh.Details.CoreLang where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import           Data.Unique

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
resolveEdhCtxAttr ets !scope !key =
  iopdLookup key (scopeEntity scope) >>= \case
    Nothing   -> resolveLexicalAttr ets (outerScopeOf scope) key
    Just !val -> return $ Just (val, scope)
{-# INLINE resolveEdhCtxAttr #-}

resolveLexicalAttr
  :: EdhThreadState -> Maybe Scope -> AttrKey -> STM (Maybe (EdhValue, Scope))
resolveLexicalAttr _ Nothing _ = return Nothing
resolveLexicalAttr ets (Just !scope) !key =
  iopdLookup key (scopeEntity scope) >>= \case
    Nothing   -> resolveLexicalAttr ets (outerScopeOf scope) key
    Just !val -> return $ Just (val, scope)
{-# INLINE resolveLexicalAttr #-}


-- * Edh effectful attribute resolution


edhEffectsMagicName :: Text
edhEffectsMagicName = "__effects__"

resolveEffectfulAttr
  :: EdhThreadState -> [Scope] -> EdhValue -> STM (Maybe (EdhValue, [Scope]))
resolveEffectfulAttr _ [] _ = return Nothing
resolveEffectfulAttr ets (scope : rest) !key =
  iopdLookup (AttrByName edhEffectsMagicName) (scopeEntity scope) >>= \case
    Nothing                    -> resolveEffectfulAttr ets rest key
    Just (EdhDict (Dict _ !d)) -> iopdLookup key d >>= \case
      Just val -> return $ Just (val, rest)
      Nothing  -> resolveEffectfulAttr ets rest key
-- todo crash in this case? warning may be more proper but in what way?
    _ -> resolveEffectfulAttr ets rest key
{-# INLINE resolveEffectfulAttr #-}


-- * Edh object attribute resolution


lookupEdhObjAttr :: EdhThreadState -> Object -> AttrKey -> STM EdhValue
lookupEdhObjAttr ets !this !key = lookupEdhObjAttr' ets key [this]
{-# INLINE lookupEdhObjAttr #-}

lookupEdhSuperAttr :: EdhThreadState -> Object -> AttrKey -> STM EdhValue
lookupEdhSuperAttr ets !this !key =
  readTVar (objSupers this) >>= lookupEdhObjAttr' ets key
{-# INLINE lookupEdhSuperAttr #-}


lookupEdhObjAttr' :: EdhThreadState -> AttrKey -> [Object] -> STM EdhValue
lookupEdhObjAttr' _   _    []           = return EdhNil
lookupEdhObjAttr' ets !key (obj : rest) = case objStore obj of
  HashStore !es -> iopdLookup key es >>= \case
    Just !v -> return v
    Nothing -> lookupRest
  HostStore{} -> lookupRest
 where
  lookupRest = do
    supers <- readTVar (objSupers obj)
    lookupEdhObjAttr' ets
                      key -- go depth first
                      (supers ++ rest)
{-# INLINE lookupEdhObjAttr' #-}


-- * Edh inheritance resolution


resolveEdhInstance :: EdhThreadState -> Unique -> Object -> STM (Maybe Object)
resolveEdhInstance ets !classUniq !that =
  resolveEdhInstance' ets classUniq [that]
{-# INLINE resolveEdhInstance #-}
resolveEdhInstance'
  :: EdhThreadState -> Unique -> [Object] -> STM (Maybe Object)
resolveEdhInstance' _ _ [] = return Nothing
resolveEdhInstance' ets !classUniq (obj : rest)
  | procedure'uniq (objClass obj) == classUniq = return (Just obj)
  | otherwise = resolveEdhInstance' ets classUniq . (rest ++) =<< readTVar
    (objSupers obj)
{-# INLINE resolveEdhInstance' #-}
