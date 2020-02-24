
-- | core language functionalities
module Language.Edh.Details.CoreLang where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map
import qualified Data.List.NonEmpty            as NE

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes


-- | resolve an attribute addressor, either alphanumeric named or symbolic
resolveAddr :: EdhProgState -> AttrAddressor -> STM AttrKey
resolveAddr _ (NamedAttr !attrName) = return (AttrByName attrName)
resolveAddr !pgs (SymbolicAttr !symName) =
  let scope = contextScope $ edh'context pgs
  in  resolveEdhCtxAttr scope (AttrByName symName) >>= \case
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


lookupEdhCtxAttr :: Scope -> AttrKey -> STM (Maybe EdhValue)
lookupEdhCtxAttr fromScope addr = resolveEdhCtxAttr fromScope addr >>= \case
  Nothing                       -> return Nothing
  Just (OriginalValue !val _ _) -> return $ Just val
{-# INLINE lookupEdhCtxAttr #-}

lookupEdhObjAttr :: Object -> AttrKey -> STM (Maybe EdhValue)
lookupEdhObjAttr this addr = resolveEdhObjAttr this addr >>= \case
  Nothing                       -> return Nothing
  Just (OriginalValue !val _ _) -> return $ Just val
{-# INLINE lookupEdhObjAttr #-}

lookupEdhSuperAttr :: Object -> AttrKey -> STM (Maybe EdhValue)
lookupEdhSuperAttr this addr = resolveEdhSuperAttr this addr >>= \case
  Nothing                       -> return Nothing
  Just (OriginalValue !val _ _) -> return $ Just val
{-# INLINE lookupEdhSuperAttr #-}


resolveEdhCtxAttr :: Scope -> AttrKey -> STM (Maybe OriginalValue)
resolveEdhCtxAttr scope@(Scope !ent _ _ lexi'stack _) !addr =
  readTVar ent >>= \em -> case Map.lookup addr em of
    Just !val -> return $ Just (OriginalValue val scope $ thatObject scope)
    Nothing   -> resolveLexicalAttr lexi'stack addr
{-# INLINE resolveEdhCtxAttr #-}

resolveLexicalAttr :: [Scope] -> AttrKey -> STM (Maybe OriginalValue)
resolveLexicalAttr [] _ = return Nothing
resolveLexicalAttr (scope@(Scope !ent !this !_that _ _) : outerScopes) addr =
  readTVar ent >>= \em -> case Map.lookup addr em of
    Just !val -> return $ Just (OriginalValue val scope $ thatObject scope)
    Nothing ->
      -- go for the interesting attribute from inheritance hierarchy
      -- of this context object, so a module as an object, can `extends`
      -- some objects too, in addition to the `import` mechanism
      (if ent == objEntity this
          -- go directly to supers as entity has just got negative result
          then readTVar (objSupers this) >>= resolveEdhSuperAttr' this addr
          -- context scope is different entity from this context object,
          -- start next from this object
          else resolveEdhObjAttr' this this addr
        )
        >>= \case
              Just scope'from'object -> return $ Just scope'from'object
              -- go one level outer of the lexical stack
              Nothing                -> resolveLexicalAttr outerScopes addr
{-# INLINE resolveLexicalAttr #-}

resolveEdhObjAttr :: Object -> AttrKey -> STM (Maybe OriginalValue)
resolveEdhObjAttr !this !addr = resolveEdhObjAttr' this this addr
{-# INLINE resolveEdhObjAttr #-}

resolveEdhSuperAttr :: Object -> AttrKey -> STM (Maybe OriginalValue)
resolveEdhSuperAttr !this !addr =
  readTVar (objSupers this) >>= resolveEdhSuperAttr' this addr
{-# INLINE resolveEdhSuperAttr #-}

resolveEdhObjAttr' :: Object -> Object -> AttrKey -> STM (Maybe OriginalValue)
resolveEdhObjAttr' !that !this !addr = readTVar thisEnt >>= \em ->
  case Map.lookup addr em of
    Just !val ->
      return
        $ Just
        $ (OriginalValue
            val
            (Scope thisEnt
                   this
                   that
                   (NE.toList $ classLexiStack $ objClass this)
                   clsProc
            )
            that
          )
    Nothing -> readTVar (objSupers this) >>= resolveEdhSuperAttr' that addr
 where
  !thisEnt = objEntity this
  clsProc  = classProcedure (objClass this)
{-# INLINE resolveEdhObjAttr' #-}

resolveEdhSuperAttr'
  :: Object -> AttrKey -> [Object] -> STM (Maybe OriginalValue)
resolveEdhSuperAttr' _ _ [] = return Nothing
resolveEdhSuperAttr' !that !addr (super : restSupers) =
  resolveEdhObjAttr' that super addr >>= \case
    Just scope -> return $ Just scope
    Nothing    -> resolveEdhSuperAttr' that addr restSupers
{-# INLINE resolveEdhSuperAttr' #-}


resolveEdhInstance' :: Class -> [Object] -> STM (Maybe Object)
resolveEdhInstance' _ [] = return Nothing
resolveEdhInstance' !class_ (obj : rest)
  | objClass obj == class_ = return (Just obj)
  | otherwise = resolveEdhInstance' class_ . (rest ++) =<< readTVar
    (objSupers obj)
{-# INLINE resolveEdhInstance' #-}
resolveEdhInstance :: Class -> Object -> STM (Maybe Object)
resolveEdhInstance !class_ !this = resolveEdhInstance' class_ [this]
{-# INLINE resolveEdhInstance #-}
