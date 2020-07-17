
-- | core language functionalities
module Language.Edh.Details.CoreLang where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import           Data.Unique

import           Language.Edh.Details.RtTypes


-- * Edh lexical attribute resolution

lookupEdhCtxAttr :: EdhProgState -> Scope -> AttrKey -> STM EdhValue
lookupEdhCtxAttr pgs !fromScope !addr =
  resolveEdhCtxAttr pgs fromScope addr >>= \case
    Nothing        -> return EdhNil
    Just (!val, _) -> return val
{-# INLINE lookupEdhCtxAttr #-}

resolveEdhCtxAttr
  :: EdhProgState -> Scope -> AttrKey -> STM (Maybe (EdhValue, Scope))
resolveEdhCtxAttr pgs !scope !addr =
  lookupEntityAttr pgs (scopeEntity scope) addr >>= \case
    EdhNil -> resolveLexicalAttr pgs (outerScopeOf scope) addr
    val    -> return $ Just (val, scope)
{-# INLINE resolveEdhCtxAttr #-}

resolveLexicalAttr
  :: EdhProgState -> Maybe Scope -> AttrKey -> STM (Maybe (EdhValue, Scope))
resolveLexicalAttr _ Nothing _ = return Nothing
resolveLexicalAttr pgs (Just !scope) !addr =
  lookupEntityAttr pgs (scopeEntity scope) addr >>= \case
    EdhNil -> resolveLexicalAttr pgs (outerScopeOf scope) addr
    !val   -> return $ Just (val, scope)
{-# INLINE resolveLexicalAttr #-}


-- * Edh effectful attribute resolution


edhEffectsMagicName :: Text
edhEffectsMagicName = "__effects__"

resolveEffectfulAttr
  :: EdhProgState -> [Scope] -> EdhValue -> STM (Maybe (EdhValue, [Scope]))
resolveEffectfulAttr _ [] _ = return Nothing
resolveEffectfulAttr pgs (scope : rest) !key =
  lookupEntityAttr pgs (scopeEntity scope) (AttrByName edhEffectsMagicName)
    >>= \case
          EdhNil               -> resolveEffectfulAttr pgs rest key
          EdhDict (Dict _ !ds) -> do
            d <- readTVar ds
            case iopdLookup key d of
              Just val -> return $ Just (val, rest)
              Nothing  -> resolveEffectfulAttr pgs rest key
  -- todo crash in this case? warning may be more proper but in what way?
          _ -> resolveEffectfulAttr pgs rest key
{-# INLINE resolveEffectfulAttr #-}


-- * Edh object attribute resolution


lookupEdhObjAttr :: EdhProgState -> Object -> AttrKey -> STM EdhValue
lookupEdhObjAttr pgs !this !addr = lookupEdhObjAttr' pgs addr [this]
{-# INLINE lookupEdhObjAttr #-}

lookupEdhSuperAttr :: EdhProgState -> Object -> AttrKey -> STM EdhValue
lookupEdhSuperAttr pgs !this !addr =
  readTVar (objSupers this) >>= lookupEdhObjAttr' pgs addr
{-# INLINE lookupEdhSuperAttr #-}


lookupEdhObjAttr' :: EdhProgState -> AttrKey -> [Object] -> STM EdhValue
lookupEdhObjAttr' _ _ [] = return EdhNil
lookupEdhObjAttr' pgs !addr (obj : rest) =
  lookupEntityAttr pgs (objEntity obj) addr >>= \case
    EdhNil -> do
      supers <- readTVar (objSupers obj)
      lookupEdhObjAttr' pgs
                        addr -- go depth first
                        (supers ++ rest)
    v -> return v
{-# INLINE lookupEdhObjAttr' #-}


-- * Edh inheritance resolution


resolveEdhInstance :: EdhProgState -> Unique -> Object -> STM (Maybe Object)
resolveEdhInstance pgs !classUniq !this =
  resolveEdhInstance' pgs classUniq [this]
{-# INLINE resolveEdhInstance #-}
resolveEdhInstance' :: EdhProgState -> Unique -> [Object] -> STM (Maybe Object)
resolveEdhInstance' _ _ [] = return Nothing
resolveEdhInstance' pgs !classUniq (obj : rest)
  | procedure'uniq (objClass obj) == classUniq = return (Just obj)
  | otherwise = resolveEdhInstance' pgs classUniq . (rest ++) =<< readTVar
    (objSupers obj)
{-# INLINE resolveEdhInstance' #-}
