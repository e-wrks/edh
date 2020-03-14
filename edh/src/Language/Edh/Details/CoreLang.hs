
-- | core language functionalities
module Language.Edh.Details.CoreLang where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import qualified Data.Text                     as T

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes


-- | resolve an attribute addressor, either alphanumeric named or symbolic
resolveAddr :: EdhProgState -> AttrAddressor -> STM AttrKey
resolveAddr _ (NamedAttr !attrName) = return (AttrByName attrName)
resolveAddr !pgs (SymbolicAttr !symName) =
  let scope = contextScope $ edh'context pgs
  in  resolveEdhCtxAttr pgs scope (AttrByName symName) >>= \case
        Just (OriginalValue !val _ _) -> case val of
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
{-# INLINE resolveAddr #-}


-- * Edh attribute resolution


lookupEdhCtxAttr :: EdhProgState -> Scope -> AttrKey -> STM EdhValue
lookupEdhCtxAttr pgs fromScope addr =
  resolveEdhCtxAttr pgs fromScope addr >>= \case
    Nothing                       -> return EdhNil
    Just (OriginalValue !val _ _) -> return val
{-# INLINE lookupEdhCtxAttr #-}

lookupEdhObjAttr :: EdhProgState -> Object -> AttrKey -> STM EdhValue
lookupEdhObjAttr pgs this addr = resolveEdhObjAttr pgs this addr >>= \case
  Nothing                       -> return EdhNil
  Just (OriginalValue !val _ _) -> return val
{-# INLINE lookupEdhObjAttr #-}

lookupEdhSuperAttr :: EdhProgState -> Object -> AttrKey -> STM EdhValue
lookupEdhSuperAttr pgs this addr = resolveEdhSuperAttr pgs this addr >>= \case
  Nothing                       -> return EdhNil
  Just (OriginalValue !val _ _) -> return val
{-# INLINE lookupEdhSuperAttr #-}


resolveEdhCtxAttr
  :: EdhProgState -> Scope -> AttrKey -> STM (Maybe OriginalValue)
resolveEdhCtxAttr pgs !scope !addr =
  lookupEntityAttr pgs (scopeEntity scope) addr >>= \case
    EdhNil -> resolveLexicalAttr pgs (outerScopeOf scope) addr
    val    -> return $ Just (OriginalValue val scope $ thatObject scope)
{-# INLINE resolveEdhCtxAttr #-}

resolveLexicalAttr
  :: EdhProgState -> Maybe Scope -> AttrKey -> STM (Maybe OriginalValue)
resolveLexicalAttr _ Nothing _ = return Nothing
resolveLexicalAttr pgs (Just scope@(Scope !ent !this !_that _)) addr =
  lookupEntityAttr pgs ent addr >>= \case
    EdhNil ->
      -- go for the interesting attribute from inheritance hierarchy
      -- of this context object, so a module as an object, can `extends`
      -- some objects too, in addition to the `import` mechanism
      (if ent == objEntity this
          -- go directly to supers as entity has just got negative result
          then readTVar (objSupers this) >>= resolveEdhSuperAttr' pgs this addr
          -- context scope is different entity from this context object,
          -- start next from this object
          else resolveEdhObjAttr' pgs this this addr
        )
        >>= \case
              Just scope'from'object -> return $ Just scope'from'object
              -- go one level outer of the lexical stack
              Nothing -> resolveLexicalAttr pgs (outerScopeOf scope) addr
    !val -> return $ Just (OriginalValue val scope $ thatObject scope)
{-# INLINE resolveLexicalAttr #-}

resolveEdhObjAttr
  :: EdhProgState -> Object -> AttrKey -> STM (Maybe OriginalValue)
resolveEdhObjAttr pgs !this !addr = resolveEdhObjAttr' pgs this this addr
{-# INLINE resolveEdhObjAttr #-}

resolveEdhSuperAttr
  :: EdhProgState -> Object -> AttrKey -> STM (Maybe OriginalValue)
resolveEdhSuperAttr pgs !this !addr =
  readTVar (objSupers this) >>= resolveEdhSuperAttr' pgs this addr
{-# INLINE resolveEdhSuperAttr #-}

resolveEdhObjAttr'
  :: EdhProgState -> Object -> Object -> AttrKey -> STM (Maybe OriginalValue)
resolveEdhObjAttr' pgs !that !this !addr =
  lookupEntityAttr pgs thisEnt addr >>= \case
    EdhNil -> readTVar (objSupers this) >>= resolveEdhSuperAttr' pgs that addr
    !val   -> return $ Just $ OriginalValue val clsScope that
 where
  !thisEnt  = objEntity this
  !clsScope = Scope thisEnt this that $ objClass this
{-# INLINE resolveEdhObjAttr' #-}

resolveEdhSuperAttr'
  :: EdhProgState -> Object -> AttrKey -> [Object] -> STM (Maybe OriginalValue)
resolveEdhSuperAttr' _ _ _ [] = return Nothing
resolveEdhSuperAttr' pgs !that !addr (super : restSupers) =
  resolveEdhObjAttr' pgs that super addr >>= \case
    Just scope -> return $ Just scope
    Nothing    -> resolveEdhSuperAttr' pgs that addr restSupers
{-# INLINE resolveEdhSuperAttr' #-}


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
