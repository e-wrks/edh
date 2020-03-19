
-- | core language functionalities
module Language.Edh.Details.CoreLang where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import qualified Data.Text                     as T

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes


-- * Edh context attribute resolution


-- | resolve an attribute addressor, either alphanumeric named or symbolic
resolveEdhAttrAddr :: EdhProgState -> AttrAddressor -> STM AttrKey
resolveEdhAttrAddr _ (NamedAttr !attrName) = return (AttrByName attrName)
resolveEdhAttrAddr !pgs (SymbolicAttr !symName) =
  let scope = contextScope $ edh'context pgs
  in  resolveEdhCtxAttr pgs scope (AttrByName symName) >>= \case
        Just (!val, _) -> case val of
          (EdhSymbol !symVal) -> return (AttrBySym symVal)
          _ ->
            throwEdhSTM pgs EvalError
              $  "Not a symbol as "
              <> symName
              <> ", it is a "
              <> T.pack (show $ edhTypeOf val)
              <> ": "
              <> T.pack (show val)
        Nothing ->
          throwEdhSTM pgs EvalError
            $  "No symbol named "
            <> T.pack (show symName)
            <> " available"
{-# INLINE resolveEdhAttrAddr #-}


lookupEdhCtxAttr :: EdhProgState -> Scope -> AttrKey -> STM EdhValue
lookupEdhCtxAttr pgs fromScope addr =
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


resolveEdhInstance' :: EdhProgState -> Class -> [Object] -> STM (Maybe Object)
resolveEdhInstance' _ _ [] = return Nothing
resolveEdhInstance' pgs !class_ (obj : rest)
  | objClass obj == class_ = return (Just obj)
  | otherwise = resolveEdhInstance' pgs class_ . (rest ++) =<< readTVar
    (objSupers obj)
{-# INLINE resolveEdhInstance' #-}
resolveEdhInstance :: EdhProgState -> Class -> Object -> STM (Maybe Object)
resolveEdhInstance pgs !class_ !this = resolveEdhInstance' pgs class_ [this]
{-# INLINE resolveEdhInstance #-}
