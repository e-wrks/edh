{-# LANGUAGE PatternSynonyms #-}

module Language.Edh.InterOp where


import           Prelude

import           GHC.Conc                       ( unsafeIOToSTM )
-- import           System.IO.Unsafe               ( unsafePerformIO )

import           GHC.TypeLits                   ( KnownSymbol
                                                , symbolVal
                                                )

import           Control.Concurrent.STM

import           Data.Unique
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.ByteString                ( ByteString )
import qualified Data.HashMap.Strict           as Map

import           Data.Proxy
import           Data.Dynamic

import qualified Data.UUID                     as UUID

import           Data.Lossless.Decimal         as D

import           Language.Edh.Args
import           Language.Edh.Control

import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


mkIntrinsicOp :: EdhWorld -> OpSymbol -> EdhIntrinsicOp -> STM EdhValue
mkIntrinsicOp !world !opSym !iop = do
  u <- unsafeIOToSTM newUnique
  Map.lookup opSym <$> readTMVar (edh'world'operators world) >>= \case
    Nothing ->
      throwSTM
        $ EdhError
            UsageError
            ("no precedence declared in the world for operator: " <> opSym)
            (toDyn nil)
        $ EdhCallContext "<edh>" []
    Just (preced, _) -> return
      $ EdhProcedure (EdhIntrOp preced $ IntrinOpDefi u opSym iop) Nothing


-- | Class for a procedure implemented in the host language (which is Haskell)
-- that can be called from Edh code.
--
-- Note the top frame of the call stack from thread state is the one for the
-- callee, that scope should have mounted the caller's scope entity, not a new
-- entity in contrast to when an Edh procedure as the callee.
class EdhCallable fn where
  callFromEdh :: fn -> ArgsPack -> EdhTxExit -> EdhTx


-- nullary base case
instance EdhCallable (EdhTxExit -> EdhTx) where
  callFromEdh !fn apk@(ArgsPack !args !kwargs) !exit =
    if null args && odNull kwargs
      then fn exit
      else \ !ets -> edhValueRepr ets (EdhArgsPack apk) $ \ !badRepr ->
        throwEdh ets UsageError $ "extraneous arguments: " <> badRepr

-- repack rest-positional-args
instance EdhCallable fn' => EdhCallable ([EdhValue] -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    callFromEdh (fn args) (ArgsPack [] kwargs) exit

-- repack rest-keyword-args
instance EdhCallable fn' => EdhCallable (OrderedDict AttrKey EdhValue -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    callFromEdh (fn kwargs) (ArgsPack args odEmpty) exit

-- repack rest-pack-args
-- note it'll cause runtime error if @fn'@ takes further args
instance EdhCallable fn' => EdhCallable (ArgsPack -> fn') where
  callFromEdh !fn !apk !exit = callFromEdh (fn apk) (ArgsPack [] odEmpty) exit

-- receive positional-only arg taking 'EdhValue'
instance EdhCallable fn' => EdhCallable (EdhValue -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit =
    callFromEdh (fn val) (ArgsPack args kwargs) exit
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'EdhValue'
instance EdhCallable fn' => EdhCallable (Maybe EdhValue -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit =
    callFromEdh (fn (Just val)) (ArgsPack args kwargs) exit

-- receive positional-only arg taking 'EdhTypeValue'
instance EdhCallable fn' => EdhCallable (EdhTypeValue -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhType !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'EdhTypeValue'
instance EdhCallable fn' => EdhCallable (Maybe EdhTypeValue -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhType !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'Decimal'
instance EdhCallable fn' => EdhCallable (Decimal -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _                -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'Decimal'
instance EdhCallable fn' => EdhCallable (Maybe Decimal -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' ->
      callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'Bool'
instance EdhCallable fn' => EdhCallable (Bool -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBool !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'Bool'
instance EdhCallable fn' => EdhCallable (Maybe Bool -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBool !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'Blob'
instance EdhCallable fn' => EdhCallable (ByteString -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBlob !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'Blob'
instance EdhCallable fn' => EdhCallable (Maybe ByteString -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBlob !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'Text'
instance EdhCallable fn' => EdhCallable (Text -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhString !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _               -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'Text'
instance EdhCallable fn' => EdhCallable (Maybe Text -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhString !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _               -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'Symbol'
instance EdhCallable fn' => EdhCallable (Symbol -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhSymbol !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _               -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'Symbol'
instance EdhCallable fn' => EdhCallable (Maybe Symbol -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhSymbol !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _               -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'UUID'
instance EdhCallable fn' => EdhCallable (UUID.UUID -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhUUID !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'UUID'
instance EdhCallable fn' => EdhCallable (Maybe UUID.UUID -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhUUID !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'EdhPair'
instance EdhCallable fn' => EdhCallable ((EdhValue, EdhValue) -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhPair !v1 !v2 -> callFromEdh (fn (v1, v2)) (ArgsPack args kwargs) exit
    _               -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'EdhPair'
instance EdhCallable fn' => EdhCallable (Maybe (EdhValue, EdhValue) -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhPair !v1 !v2 ->
      callFromEdh (fn (Just (v1, v2))) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'Dict'
instance EdhCallable fn' => EdhCallable (Dict -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDict !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'Dict'
instance EdhCallable fn' => EdhCallable (Maybe Dict -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDict !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'List'
instance EdhCallable fn' => EdhCallable (List -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhList !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'List'
instance EdhCallable fn' => EdhCallable (Maybe List -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhList !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'Object'
instance EdhCallable fn' => EdhCallable (Object -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhObject !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _               -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'Object'
instance EdhCallable fn' => EdhCallable (Maybe Object -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhObject !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _               -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'EdhOrd'
instance EdhCallable fn' => EdhCallable (Ordering -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhOrd !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _            -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'EdhOrd'
instance EdhCallable fn' => EdhCallable (Maybe Ordering -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhOrd !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _            -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'EventSink'
instance EdhCallable fn' => EdhCallable (EventSink -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhSink !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'EventSink'
instance EdhCallable fn' => EdhCallable (Maybe EventSink -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhSink !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _             -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'EdhNamedValue'
instance EdhCallable fn' => EdhCallable ((AttrName,EdhValue) -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhNamedValue !name !value ->
      callFromEdh (fn (name, value)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'EdhNamedValue'
instance EdhCallable fn' => EdhCallable (Maybe (AttrName,EdhValue) -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhNamedValue !name !value ->
      callFromEdh (fn (Just (name, value))) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive positional-only arg taking 'EdhExpr'
instance EdhCallable fn' => EdhCallable ((Expr,Text) -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhExpr _ !expr !src ->
      callFromEdh (fn (expr, src)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive positional-only, optional arg taking 'EdhExpr'
instance EdhCallable fn' => EdhCallable (Maybe (Expr,Text) -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhExpr _ !expr !src ->
      callFromEdh (fn (Just (expr, src))) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"


-- receive named arg taking 'EdhValue'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg EdhValue name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, kwargs') ->
        callFromEdh (fn (NamedArg val)) (ArgsPack args kwargs') exit
      (Nothing, kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        (val : args') ->
          callFromEdh (fn (NamedArg val)) (ArgsPack args' kwargs') exit
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhValue'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe EdhValue) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' ->
          callFromEdh (fn (NamedArg (Just val))) (ArgsPack args' kwargs') exit
      (!maybeVal, !kwargs') ->
        callFromEdh (fn (NamedArg maybeVal)) (ArgsPack args kwargs') exit
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhTypeValue'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg EdhTypeValue name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhType !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhType !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhTypeValue'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe EdhTypeValue) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhType !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhType !val' -> callFromEdh (fn (NamedArg (Just val')))
                                       (ArgsPack args' kwargs')
                                       exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Decimal'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg Decimal name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Decimal'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe Decimal) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDecimal !val' -> callFromEdh (fn (NamedArg (Just val')))
                                          (ArgsPack args' kwargs')
                                          exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Bool'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg Bool name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBool !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhBool !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Bool'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe Bool) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBool !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhBool !val' -> callFromEdh (fn (NamedArg (Just val')))
                                       (ArgsPack args' kwargs')
                                       exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'ByteString'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg ByteString name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBlob !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhBlob !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'ByteString'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe ByteString) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBlob !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhBlob !val' -> callFromEdh (fn (NamedArg (Just val')))
                                       (ArgsPack args' kwargs')
                                       exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Text'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg Text name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhString !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhString !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Text'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe Text) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhString !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhString !val' -> callFromEdh (fn (NamedArg (Just val')))
                                         (ArgsPack args' kwargs')
                                         exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Symbol'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg Symbol name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSymbol !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhSymbol !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Symbol'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe Symbol) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSymbol !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhSymbol !val' -> callFromEdh (fn (NamedArg (Just val')))
                                         (ArgsPack args' kwargs')
                                         exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'UUID'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg UUID.UUID name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhUUID !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhUUID !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'UUID'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe UUID.UUID) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhUUID !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhUUID !val' -> callFromEdh (fn (NamedArg (Just val')))
                                       (ArgsPack args' kwargs')
                                       exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhPair'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (EdhValue, EdhValue) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhPair !v1 !v2 ->
          callFromEdh (fn (NamedArg (v1, v2))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhPair !v1 !v2 ->
            callFromEdh (fn (NamedArg (v1, v2))) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhPair'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe (EdhValue, EdhValue)) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhPair !v1 !v2 -> callFromEdh (fn (NamedArg (Just (v1, v2))))
                                       (ArgsPack args kwargs')
                                       exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhPair !v1 !v2 -> callFromEdh (fn (NamedArg (Just (v1, v2))))
                                         (ArgsPack args' kwargs')
                                         exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Dict'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg Dict name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDict !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDict !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Dict'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe Dict) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDict !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDict !val' -> callFromEdh (fn (NamedArg (Just val')))
                                       (ArgsPack args' kwargs')
                                       exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'List'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg List name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhList !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhList !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'List'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe List) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhList !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhList !val' -> callFromEdh (fn (NamedArg (Just val')))
                                       (ArgsPack args' kwargs')
                                       exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Object'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg Object name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhObject !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Object'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe Object) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhObject !val' -> callFromEdh (fn (NamedArg (Just val')))
                                         (ArgsPack args' kwargs')
                                         exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Ordering'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg Ordering name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhOrd !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhOrd !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Ordering'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe Ordering) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhOrd !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhOrd !val' -> callFromEdh (fn (NamedArg (Just val')))
                                      (ArgsPack args' kwargs')
                                      exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EventSink'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg EventSink name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSink !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhSink !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EventSink'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe EventSink) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSink !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhSink !val' -> callFromEdh (fn (NamedArg (Just val')))
                                       (ArgsPack args' kwargs')
                                       exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhNamedValue'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (AttrName,EdhValue) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhNamedValue !name !value ->
          callFromEdh (fn (NamedArg (name, value))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhNamedValue !name !value -> callFromEdh
            (fn (NamedArg (name, value)))
            (ArgsPack args' kwargs')
            exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhNamedValue'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe (AttrName,EdhValue)) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhNamedValue !name !value -> callFromEdh
          (fn (NamedArg (Just (name, value))))
          (ArgsPack args kwargs')
          exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhNamedValue !name !value -> callFromEdh
            (fn (NamedArg (Just (name, value))))
            (ArgsPack args' kwargs')
            exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhExpr'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Expr,Text) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr _ !expr !src ->
          callFromEdh (fn (NamedArg (expr, src))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhExpr _ !expr !src -> callFromEdh (fn (NamedArg (expr, src)))
                                              (ArgsPack args' kwargs')
                                              exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhExpr'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe (Expr,Text)) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr _ !expr !src -> callFromEdh
          (fn (NamedArg (Just (expr, src))))
          (ArgsPack args kwargs')
          exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhExpr _ !expr !src -> callFromEdh
            (fn (NamedArg (Just (expr, src))))
            (ArgsPack args' kwargs')
            exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'ArgsPack'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg ArgsPack name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack !val' ->
          callFromEdh (fn (NamedArg val')) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        []          -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack !val' ->
            callFromEdh (fn (NamedArg val')) (ArgsPack args' kwargs') exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'ArgsPack'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedArg (Maybe ArgsPack) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack !val' ->
          callFromEdh (fn (NamedArg (Just val'))) (ArgsPack args kwargs') exit
        _ -> throwEdhTx UsageError "arg type mismatch"
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhArgsPack !val' -> callFromEdh (fn (NamedArg (Just val')))
                                           (ArgsPack args' kwargs')
                                           exit
          _ -> throwEdhTx UsageError "arg type mismatch"
    where !argName = T.pack $ symbolVal (Proxy :: Proxy name)


wrapHostProc :: EdhCallable fn => fn -> (ArgsPack -> EdhHostProc, ArgsReceiver)
wrapHostProc !fn = -- TODO derive arg receivers (procedure signature)
  (callFromEdh fn, WildReceiver)


mkHostProc
  :: Scope
  -> (ProcDefi -> EdhProc)
  -> AttrName
  -> (ArgsPack -> EdhHostProc, ArgsReceiver)
  -> STM EdhValue
mkHostProc !scope !vc !nm (!p, !args) = do
  !u <- unsafeIOToSTM newUnique
  return $ EdhProcedure
    (vc ProcDefi
      { edh'procedure'ident = u
      , edh'procedure'name  = AttrByName nm
      , edh'procedure'lexi  = scope
      , edh'procedure'decl  = ProcDecl { edh'procedure'addr = NamedAttr nm
                                       , edh'procedure'args = args
                                       , edh'procedure'body = Right p
                                       }
      }
    )
    Nothing
mkHostProc'
  :: EdhCallable fn
  => Scope
  -> (ProcDefi -> EdhProc)
  -> AttrName
  -> fn
  -> STM EdhValue
mkHostProc' !scope !vc !nm !fn = mkHostProc scope vc nm $ wrapHostProc fn


mkSymbolicHostProc
  :: Scope
  -> (ProcDefi -> EdhProc)
  -> Symbol
  -> (ArgsPack -> EdhHostProc, ArgsReceiver)
  -> STM EdhValue
mkSymbolicHostProc !scope !vc !sym (!p, !args) = do
  !u <- unsafeIOToSTM newUnique
  return $ EdhProcedure
    (vc ProcDefi
      { edh'procedure'ident = u
      , edh'procedure'name  = AttrBySym sym
      , edh'procedure'lexi  = scope
      , edh'procedure'decl  = ProcDecl
                                { edh'procedure'addr = SymbolicAttr
                                                         $ symbolName sym
                                , edh'procedure'args = args
                                , edh'procedure'body = Right $ callFromEdh p
                                }
      }
    )
    Nothing
mkSymbolicHostProc'
  :: EdhCallable fn
  => Scope
  -> (ProcDefi -> EdhProc)
  -> Symbol
  -> fn
  -> STM EdhValue
mkSymbolicHostProc' !scope !vc !sym !fn =
  mkSymbolicHostProc scope vc sym $ wrapHostProc fn


mkHostProperty
  :: Scope
  -> AttrName
  -> EdhHostProc
  -> Maybe (Maybe EdhValue -> EdhHostProc)
  -> STM EdhValue
mkHostProperty !scope !nm !getterProc !maybeSetterProc = do
  getter <- do
    u <- unsafeIOToSTM newUnique
    return $ ProcDefi
      { edh'procedure'ident = u
      , edh'procedure'name  = AttrByName nm
      , edh'procedure'lexi  = scope
      , edh'procedure'decl  = ProcDecl
        { edh'procedure'addr = NamedAttr nm
        , edh'procedure'args = PackReceiver []
        , edh'procedure'body = Right $ callFromEdh getterProc
        }
      }
  setter <- case maybeSetterProc of
    Nothing          -> return Nothing
    Just !setterProc -> do
      u <- unsafeIOToSTM newUnique
      return $ Just $ ProcDefi
        { edh'procedure'ident = u
        , edh'procedure'name  = AttrByName nm
        , edh'procedure'lexi  = scope
        , edh'procedure'decl  = ProcDecl
          { edh'procedure'addr = NamedAttr nm
          , edh'procedure'args = PackReceiver
            [ RecvArg (NamedAttr "newValue") Nothing
              $ Just
              $ LitExpr
              $ ValueLiteral edhNone
            ]
          , edh'procedure'body = Right $ callFromEdh setterProc
          }
        }
  return $ EdhProcedure (EdhDescriptor getter setter) Nothing

