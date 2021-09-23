module Language.Edh.InterOp where

import Control.Concurrent.STM
import Data.ByteString (ByteString)
import Data.Dynamic
import Data.Lossless.Decimal (Decimal)
import qualified Data.Lossless.Decimal as D
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.UUID as UUID
import Data.Unique (newUnique)
import GHC.Conc (unsafeIOToSTM)
import GHC.TypeLits (KnownSymbol, symbolVal)
import Language.Edh.Args
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.RtTypes
import Type.Reflection
import Prelude

-- * utilities

wrapHostProc :: EdhCallable fn => fn -> (ArgsPack -> EdhHostProc, ArgsReceiver)
wrapHostProc !fn =
  -- TODO derive arg receivers (procedure signature)
  (callFromEdh fn, NullaryReceiver)

mkHostProc' ::
  EdhCallable fn =>
  Scope ->
  (ProcDefi -> EdhProcDefi) ->
  AttrName ->
  fn ->
  STM EdhValue
mkHostProc' !scope !vc !nm !fn = mkHostProc scope vc nm $ wrapHostProc fn

mkSymbolicHostProc' ::
  EdhCallable fn =>
  Scope ->
  (ProcDefi -> EdhProcDefi) ->
  Symbol ->
  fn ->
  STM EdhValue
mkSymbolicHostProc' !scope !vc !sym !fn =
  mkSymbolicHostProc scope vc sym $ wrapHostProc fn

-- * type level helper classes & instances

-- | Class for an object allocator implemented in the host language (which is
-- Haskell) that can be called from Edh code.
class EdhAllocator fn where
  allocEdhObj :: fn -> ArgsPack -> EdhAllocExit -> EdhTx

-- nullary base case
instance EdhAllocator (EdhAllocExit -> EdhTx) where
  allocEdhObj !fn apk@(ArgsPack !args !kwargs) !exit =
    if null args && odNull kwargs
      then fn exit
      else \ !ets -> edhValueRepr ets (EdhArgsPack apk) $ \ !badRepr ->
        throwEdh ets UsageError $ "extraneous arguments: " <> badRepr

-- repack rest-positional-args
instance EdhAllocator fn' => EdhAllocator ([EdhValue] -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    allocEdhObj (fn args) (ArgsPack [] kwargs) exit

instance EdhAllocator fn' => EdhAllocator (NamedEdhArg [EdhValue] name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    allocEdhObj (fn (NamedEdhArg args)) (ArgsPack [] kwargs) exit

-- repack rest-keyword-args
instance EdhAllocator fn' => EdhAllocator (KwArgs -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    allocEdhObj (fn kwargs) (ArgsPack args odEmpty) exit

instance EdhAllocator fn' => EdhAllocator (NamedEdhArg KwArgs name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    allocEdhObj (fn (NamedEdhArg kwargs)) (ArgsPack args odEmpty) exit

-- repack rest-pack-args
--
-- note it'll cause runtime error if @fn'@ takes further args
-- todo detect that case and report static errors?
instance EdhAllocator fn' => EdhAllocator (ArgsPack -> fn') where
  allocEdhObj !fn !apk !exit = allocEdhObj (fn apk) (ArgsPack [] odEmpty) exit

instance EdhAllocator fn' => EdhAllocator (NamedEdhArg ArgsPack name -> fn') where
  allocEdhObj !fn !apk !exit =
    allocEdhObj (fn (NamedEdhArg apk)) (ArgsPack [] odEmpty) exit

-- receive anonymous arg taking 'EdhValue'
instance EdhAllocator fn' => EdhAllocator (EdhValue -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit =
    allocEdhObj (fn val) (ArgsPack args kwargs) exit
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhValue'
instance EdhAllocator fn' => EdhAllocator (Maybe EdhValue -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit =
    allocEdhObj (fn (Just val)) (ArgsPack args kwargs) exit

-- receive anonymous arg taking 'Decimal'
instance EdhAllocator fn' => EdhAllocator (Decimal -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' -> allocEdhObj (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Decimal'
instance EdhAllocator fn' => EdhAllocator (Maybe Decimal -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' ->
      allocEdhObj (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Double'
instance EdhAllocator fn' => EdhAllocator (Double -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in allocEdhObj (fn d) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Double'
instance EdhAllocator fn' => EdhAllocator (Maybe Double -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in allocEdhObj (fn (Just d)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Float'
instance EdhAllocator fn' => EdhAllocator (Float -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in allocEdhObj (fn d) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Float'
instance EdhAllocator fn' => EdhAllocator (Maybe Float -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in allocEdhObj (fn (Just d)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Integer'
instance EdhAllocator fn' => EdhAllocator (Integer -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> allocEdhObj (fn i) (ArgsPack args kwargs) exit
      _ -> throwEdhTx UsageError "number type mismatch: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Integer'
instance EdhAllocator fn' => EdhAllocator (Maybe Integer -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> allocEdhObj (fn (Just i)) (ArgsPack args kwargs) exit
      _ -> throwEdhTx UsageError "number type mismatch: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Int'
instance EdhAllocator fn' => EdhAllocator (Int -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> allocEdhObj (fn $ fromInteger i) (ArgsPack args kwargs) exit
      _ -> throwEdhTx UsageError "number type mismatch: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Int'
instance EdhAllocator fn' => EdhAllocator (Maybe Int -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i ->
        allocEdhObj (fn (Just $ fromInteger i)) (ArgsPack args kwargs) exit
      _ -> throwEdhTx UsageError "number type mismatch: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Bool'
instance EdhAllocator fn' => EdhAllocator (Bool -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBool !val' -> allocEdhObj (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Bool'
instance EdhAllocator fn' => EdhAllocator (Maybe Bool -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBool !val' -> allocEdhObj (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Blob'
instance EdhAllocator fn' => EdhAllocator (ByteString -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBlob !val' -> allocEdhObj (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Blob'
instance EdhAllocator fn' => EdhAllocator (Maybe ByteString -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBlob !val' -> allocEdhObj (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Text'
instance EdhAllocator fn' => EdhAllocator (Text -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhString !val' -> allocEdhObj (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Text'
instance EdhAllocator fn' => EdhAllocator (Maybe Text -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhString !val' -> allocEdhObj (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Symbol'
instance EdhAllocator fn' => EdhAllocator (Symbol -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhSymbol !val' -> allocEdhObj (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Symbol'
instance EdhAllocator fn' => EdhAllocator (Maybe Symbol -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhSymbol !val' -> allocEdhObj (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'UUID'
instance EdhAllocator fn' => EdhAllocator (UUID.UUID -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhUUID !val' -> allocEdhObj (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'UUID'
instance EdhAllocator fn' => EdhAllocator (Maybe UUID.UUID -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhUUID !val' -> allocEdhObj (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhPair'
instance EdhAllocator fn' => EdhAllocator ((EdhValue, EdhValue) -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhPair !v1 !v2 -> allocEdhObj (fn (v1, v2)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhPair'
instance EdhAllocator fn' => EdhAllocator (Maybe (EdhValue, EdhValue) -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhPair !v1 !v2 ->
      allocEdhObj (fn (Just (v1, v2))) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Dict'
instance EdhAllocator fn' => EdhAllocator (Dict -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDict !val' -> allocEdhObj (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Dict'
instance EdhAllocator fn' => EdhAllocator (Maybe Dict -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDict !val' -> allocEdhObj (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'List'
instance EdhAllocator fn' => EdhAllocator (List -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhList !val' -> allocEdhObj (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'List'
instance EdhAllocator fn' => EdhAllocator (Maybe List -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhList !val' -> allocEdhObj (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Object'
instance EdhAllocator fn' => EdhAllocator (Object -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhObject !obj -> allocEdhObj (fn obj) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Object'
instance EdhAllocator fn' => EdhAllocator (Maybe Object -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhObject !obj -> allocEdhObj (fn (Just obj)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhOrd'
instance EdhAllocator fn' => EdhAllocator (Ordering -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhOrd !val' -> allocEdhObj (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhOrd'
instance EdhAllocator fn' => EdhAllocator (Maybe Ordering -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhOrd !val' -> allocEdhObj (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhSink'
instance EdhAllocator fn' => EdhAllocator (EdhSink -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhEvs !val' -> allocEdhObj (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhSink'
instance EdhAllocator fn' => EdhAllocator (Maybe EdhSink -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhEvs !val' -> allocEdhObj (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhNamedValue'
instance EdhAllocator fn' => EdhAllocator ((AttrName, EdhValue) -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhNamedValue !name !value ->
      allocEdhObj (fn (name, value)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhNamedValue'
instance EdhAllocator fn' => EdhAllocator (Maybe (AttrName, EdhValue) -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhNamedValue !name !value ->
      allocEdhObj (fn (Just (name, value))) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhExpr'
instance EdhAllocator fn' => EdhAllocator (ExprDefi -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhExpr !expr _src ->
      allocEdhObj (fn expr) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhExpr'
instance EdhAllocator fn' => EdhAllocator (Maybe ExprDefi -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhExpr !expr _src ->
      allocEdhObj (fn (Just expr)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhExpr' with src
instance EdhAllocator fn' => EdhAllocator ((ExprDefi, Text) -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhExpr !expr !src ->
      allocEdhObj (fn (expr, src)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhExpr' with src
instance EdhAllocator fn' => EdhAllocator (Maybe (ExprDefi, Text) -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhExpr !expr !src ->
      allocEdhObj (fn (Just (expr, src))) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'PositionalArgs'
instance EdhAllocator fn' => EdhAllocator (PositionalArgs -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if odNull kwargs''
        then allocEdhObj (fn (PositionalArgs args'')) (ArgsPack args kwargs) exit
        else throwEdhTx UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'PositionalArgs'
instance EdhAllocator fn' => EdhAllocator (Maybe PositionalArgs -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if odNull kwargs''
        then
          allocEdhObj
            (fn (Just (PositionalArgs args'')))
            (ArgsPack args kwargs)
            exit
        else throwEdhTx UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'KeywordArgs'
instance EdhAllocator fn' => EdhAllocator (KeywordArgs -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if null args''
        then allocEdhObj (fn (KeywordArgs kwargs'')) (ArgsPack args kwargs) exit
        else throwEdhTx UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'KeywordArgs'
instance EdhAllocator fn' => EdhAllocator (Maybe KeywordArgs -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if null args''
        then
          allocEdhObj
            (fn (Just (KeywordArgs kwargs'')))
            (ArgsPack args kwargs)
            exit
        else throwEdhTx UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'PackedArgs'
instance EdhAllocator fn' => EdhAllocator (PackedArgs -> fn') where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack !apk ->
      allocEdhObj (fn (PackedArgs apk)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  allocEdhObj _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'PackedArgs'
instance EdhAllocator fn' => EdhAllocator (Maybe PackedArgs -> fn') where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit =
    allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack !apk ->
      allocEdhObj (fn (Just (PackedArgs apk))) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive named arg taking 'EdhValue'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg EdhValue name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, kwargs') ->
        allocEdhObj (fn (NamedEdhArg val)) (ArgsPack args kwargs') exit
      (Nothing, kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        (val : args') ->
          allocEdhObj (fn (NamedEdhArg val)) (ArgsPack args' kwargs') exit
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhValue'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe EdhValue) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' ->
          allocEdhObj
            (fn (NamedEdhArg (Just val)))
            (ArgsPack args' kwargs')
            exit
      (!maybeVal, !kwargs') ->
        allocEdhObj (fn (NamedEdhArg maybeVal)) (ArgsPack args kwargs') exit
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Decimal'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg Decimal name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Decimal for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Decimal for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Decimal'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe Decimal) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          allocEdhObj
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Decimal for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDecimal !val' ->
            allocEdhObj
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Decimal for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Double'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg Double name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in allocEdhObj (fn (NamedEdhArg d)) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Double for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in allocEdhObj (fn (NamedEdhArg d)) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Double for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Double'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe Double) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in allocEdhObj
                (fn (NamedEdhArg (Just d)))
                (ArgsPack args kwargs')
                exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Double for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in allocEdhObj
                  (fn (NamedEdhArg (Just d)))
                  (ArgsPack args' kwargs')
                  exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Double for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Float'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg Float name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in allocEdhObj (fn (NamedEdhArg d)) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Float for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in allocEdhObj (fn (NamedEdhArg d)) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Float for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Float'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe Float) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in allocEdhObj
                (fn (NamedEdhArg (Just d)))
                (ArgsPack args kwargs')
                exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Float for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in allocEdhObj
                  (fn (NamedEdhArg (Just d)))
                  (ArgsPack args' kwargs')
                  exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Float for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Integer'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg Integer name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            allocEdhObj (fn (NamedEdhArg i)) (ArgsPack args kwargs') exit
          _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Integer for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              allocEdhObj (fn (NamedEdhArg i)) (ArgsPack args' kwargs') exit
            _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Integer for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Integer'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe Integer) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            allocEdhObj (fn (NamedEdhArg (Just i))) (ArgsPack args kwargs') exit
          _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Integer for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              allocEdhObj
                (fn (NamedEdhArg (Just i)))
                (ArgsPack args' kwargs')
                exit
            _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Integer for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Int'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg Int name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            allocEdhObj
              (fn (NamedEdhArg $ fromInteger i))
              (ArgsPack args kwargs')
              exit
          _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Int for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              allocEdhObj
                (fn (NamedEdhArg $ fromInteger i))
                (ArgsPack args' kwargs')
                exit
            _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Int for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Int'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe Int) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            allocEdhObj
              (fn (NamedEdhArg (Just $ fromInteger i)))
              (ArgsPack args kwargs')
              exit
          _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Int for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              allocEdhObj
                (fn (NamedEdhArg (Just $ fromInteger i)))
                (ArgsPack args' kwargs')
                exit
            _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Int for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Bool'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg Bool name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBool !val' ->
          allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Bool for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhBool !val' ->
            allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Bool for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Bool'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe Bool) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBool !val' ->
          allocEdhObj
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Bool for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhBool !val' ->
            allocEdhObj
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Bool for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'ByteString'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg ByteString name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBlob !val' ->
          allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect ByteString for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhBlob !val' ->
            allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect ByteString for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'ByteString'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe ByteString) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBlob !val' ->
          allocEdhObj
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect ByteString for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhBlob !val' ->
            allocEdhObj
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect ByteString for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Text'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg Text name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhString !val' ->
          allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Text for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhString !val' ->
            allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Text for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Text'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe Text) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhString !val' ->
          allocEdhObj
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Text for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhString !val' ->
            allocEdhObj
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Text for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Symbol'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg Symbol name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSymbol !val' ->
          allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect symbol for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhSymbol !val' ->
            allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect symbol for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Symbol'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe Symbol) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSymbol !val' ->
          allocEdhObj
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect symbol for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhSymbol !val' ->
            allocEdhObj
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect symbol for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'UUID'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg UUID.UUID name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhUUID !val' ->
          allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect UUID for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhUUID !val' ->
            allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect UUID for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'UUID'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe UUID.UUID) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhUUID !val' ->
          allocEdhObj
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect UUID for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhUUID !val' ->
            allocEdhObj
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect UUID for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhPair'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (EdhValue, EdhValue) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhPair !v1 !v2 ->
          allocEdhObj (fn (NamedEdhArg (v1, v2))) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect pair for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhPair !v1 !v2 ->
            allocEdhObj
              (fn (NamedEdhArg (v1, v2)))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect pair for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhPair'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe (EdhValue, EdhValue)) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhPair !v1 !v2 ->
          allocEdhObj
            (fn (NamedEdhArg (Just (v1, v2))))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect pair for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhPair !v1 !v2 ->
            allocEdhObj
              (fn (NamedEdhArg (Just (v1, v2))))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect pair for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Dict'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg Dict name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDict !val' ->
          allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect dict for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDict !val' ->
            allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect dict for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Dict'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe Dict) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDict !val' ->
          allocEdhObj
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect dict for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDict !val' ->
            allocEdhObj
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect dict for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'List'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg List name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhList !val' ->
          allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect list for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhList !val' ->
            allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect list for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'List'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe List) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhList !val' ->
          allocEdhObj
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect list for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhList !val' ->
            allocEdhObj
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect list for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Object'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg Object name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !obj ->
          allocEdhObj (fn (NamedEdhArg obj)) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect object for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhObject !obj ->
            allocEdhObj (fn (NamedEdhArg obj)) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect object for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Object'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe Object) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !obj ->
          allocEdhObj (fn (NamedEdhArg (Just obj))) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect object for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhObject !obj ->
            allocEdhObj
              (fn (NamedEdhArg (Just obj)))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect object for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Ordering'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg Ordering name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhOrd !val' ->
          allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Ordering for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhOrd !val' ->
            allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Ordering for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Ordering'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe Ordering) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhOrd !val' ->
          allocEdhObj
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Ordering for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhOrd !val' ->
            allocEdhObj
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Ordering for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhSink'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg EdhSink name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhEvs !val' ->
          allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect sink for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhEvs !val' ->
            allocEdhObj (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect sink for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhSink'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe EdhSink) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhEvs !val' ->
          allocEdhObj
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect sink for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhEvs !val' ->
            allocEdhObj
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect sink for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhNamedValue'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (AttrName, EdhValue) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhNamedValue !name !value ->
          allocEdhObj
            (fn (NamedEdhArg (name, value)))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhNamedValue !name !value ->
            allocEdhObj
              (fn (NamedEdhArg (name, value)))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhNamedValue'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe (AttrName, EdhValue)) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhNamedValue !name !value ->
          allocEdhObj
            (fn (NamedEdhArg (Just (name, value))))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhNamedValue !name !value ->
            allocEdhObj
              (fn (NamedEdhArg (Just (name, value))))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhExpr'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg ExprDefi name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr _src ->
          allocEdhObj
            (fn (NamedEdhArg expr))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhExpr !expr _src ->
            allocEdhObj
              (fn (NamedEdhArg expr))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhExpr'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe ExprDefi) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr _src ->
          allocEdhObj
            (fn (NamedEdhArg (Just expr)))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhExpr !expr _src ->
            allocEdhObj
              (fn (NamedEdhArg (Just expr)))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhExpr' with src
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (ExprDefi, Text) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr !src ->
          allocEdhObj
            (fn (NamedEdhArg (expr, src)))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhExpr !expr !src ->
            allocEdhObj
              (fn (NamedEdhArg (expr, src)))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhExpr' with src
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe (ExprDefi, Text)) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr !src ->
          allocEdhObj
            (fn (NamedEdhArg (Just (expr, src))))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhExpr !expr !src ->
            allocEdhObj
              (fn (NamedEdhArg (Just (expr, src))))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'PositionalArgs'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg PositionalArgs name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if odNull kwargs''
            then
              allocEdhObj
                (fn (NamedEdhArg $ PositionalArgs args''))
                (ArgsPack args kwargs')
                exit
            else throwEdhTx UsageError $ "extraneous kwargs for: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect tuple for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if odNull kwargs''
              then
                allocEdhObj
                  (fn (NamedEdhArg $ PositionalArgs args''))
                  (ArgsPack args' kwargs')
                  exit
              else throwEdhTx UsageError $ "extraneous kwargs for: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect tuple for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'PositionalArgs'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe PositionalArgs) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if odNull kwargs''
            then
              allocEdhObj
                (fn (NamedEdhArg $ Just $ PositionalArgs args''))
                (ArgsPack args kwargs')
                exit
            else throwEdhTx UsageError $ "extraneous kwargs for: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect tuple for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if odNull kwargs''
              then
                allocEdhObj
                  (fn (NamedEdhArg $ Just $ PositionalArgs args''))
                  (ArgsPack args' kwargs')
                  exit
              else throwEdhTx UsageError $ "extraneous kwargs for: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect tuple for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'KeywordArgs'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg KeywordArgs name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if null args''
            then
              allocEdhObj
                (fn (NamedEdhArg $ KeywordArgs kwargs''))
                (ArgsPack args kwargs')
                exit
            else throwEdhTx UsageError $ "extraneous pos args for: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect kwargs for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if null args''
              then
                allocEdhObj
                  (fn (NamedEdhArg $ KeywordArgs kwargs''))
                  (ArgsPack args' kwargs')
                  exit
              else throwEdhTx UsageError $ "extraneous pos args for: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect kwargs for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'KeywordArgs'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe KeywordArgs) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if null args''
            then
              allocEdhObj
                (fn (NamedEdhArg $ Just $ KeywordArgs kwargs''))
                (ArgsPack args kwargs')
                exit
            else throwEdhTx UsageError $ "extraneous pos args for: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect kwargs for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if null args''
              then
                allocEdhObj
                  (fn (NamedEdhArg $ Just $ KeywordArgs kwargs''))
                  (ArgsPack args' kwargs')
                  exit
              else throwEdhTx UsageError $ "extraneous pos args for: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect kwargs for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'PackedArgs'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg PackedArgs name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack !apk ->
          allocEdhObj
            (fn (NamedEdhArg $ PackedArgs apk))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect apk for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack !apk ->
            allocEdhObj
              (fn (NamedEdhArg $ PackedArgs apk))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect apk for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'PackedArgs'
instance (KnownSymbol name, EdhAllocator fn') => EdhAllocator (NamedEdhArg (Maybe PackedArgs) name -> fn') where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack !apk ->
          allocEdhObj
            (fn (NamedEdhArg (Just $ PackedArgs apk)))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect apk for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhArgsPack !apk ->
            allocEdhObj
              (fn (NamedEdhArg (Just $ PackedArgs apk)))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect apk for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

mkIntrinsicOp :: EdhWorld -> OpSymbol -> EdhIntrinsicOp -> STM EdhValue
mkIntrinsicOp !world !opSym !iop = do
  !u <- unsafeIOToSTM newUnique
  {- HLINT ignore "Redundant <$>" -}
  lookupOpFromDict opSym <$> readTVar (edh'world'operators world) >>= \case
    Nothing ->
      throwSTM $
        EdhError
          UsageError
          ("operator (" <> opSym <> ") not declared in this world")
          (toDyn nil)
          "<edh>"
    Just (fixity, preced, _) ->
      return $
        EdhProcedure
          (EdhIntrOp fixity preced $ IntrinOpDefi u opSym iop)
          Nothing

-- | Class for a procedure implemented in the host language (which is Haskell)
-- that can be called from Edh code.
--
-- Note the top frame of the call stack from thread state is the one for the
-- callee, that scope should have mounted the caller's scope entity, not a new
-- entity in contrast to when an Edh procedure as the callee.
class EdhCallable fn where
  callFromEdh :: fn -> ArgsPack -> EdhTxExit EdhValue -> EdhTx

-- nullary base case
instance EdhCallable (EdhTxExit EdhValue -> EdhTx) where
  callFromEdh !fn apk@(ArgsPack !args !kwargs) !exit =
    if null args && odNull kwargs
      then fn exit
      else \ !ets -> edhValueRepr ets (EdhArgsPack apk) $ \ !badRepr ->
        throwEdh ets UsageError $ "extraneous arguments: " <> badRepr

-- repack rest-positional-args
instance EdhCallable fn' => EdhCallable ([EdhValue] -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    callFromEdh (fn args) (ArgsPack [] kwargs) exit

instance EdhCallable fn' => EdhCallable (NamedEdhArg [EdhValue] name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    callFromEdh (fn (NamedEdhArg args)) (ArgsPack [] kwargs) exit

-- repack rest-keyword-args
instance EdhCallable fn' => EdhCallable (KwArgs -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    callFromEdh (fn kwargs) (ArgsPack args odEmpty) exit

instance EdhCallable fn' => EdhCallable (NamedEdhArg KwArgs name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    callFromEdh (fn (NamedEdhArg kwargs)) (ArgsPack args odEmpty) exit

-- repack rest-pack-args
--
-- note it'll cause runtime error if @fn'@ takes further args
-- todo detect that case and report static errors?
instance EdhCallable fn' => EdhCallable (ArgsPack -> fn') where
  callFromEdh !fn !apk !exit = callFromEdh (fn apk) (ArgsPack [] odEmpty) exit

instance EdhCallable fn' => EdhCallable (NamedEdhArg ArgsPack name -> fn') where
  callFromEdh !fn !apk !exit =
    callFromEdh (fn (NamedEdhArg apk)) (ArgsPack [] odEmpty) exit

-- receive anonymous arg taking 'EdhValue'
instance EdhCallable fn' => EdhCallable (EdhValue -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit =
    callFromEdh (fn val) (ArgsPack args kwargs) exit
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhValue'
instance EdhCallable fn' => EdhCallable (Maybe EdhValue -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit =
    callFromEdh (fn (Just val)) (ArgsPack args kwargs) exit

-- receive anonymous arg taking 'Decimal'
instance EdhCallable fn' => EdhCallable (Decimal -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Decimal'
instance EdhCallable fn' => EdhCallable (Maybe Decimal -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' ->
      callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Double'
instance EdhCallable fn' => EdhCallable (Double -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in callFromEdh (fn d) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Double'
instance EdhCallable fn' => EdhCallable (Maybe Double -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in callFromEdh (fn (Just d)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Float'
instance EdhCallable fn' => EdhCallable (Float -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in callFromEdh (fn d) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Float'
instance EdhCallable fn' => EdhCallable (Maybe Float -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in callFromEdh (fn (Just d)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Integer'
instance EdhCallable fn' => EdhCallable (Integer -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> callFromEdh (fn i) (ArgsPack args kwargs) exit
      _ -> throwEdhTx UsageError "number type mismatch: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Integer'
instance EdhCallable fn' => EdhCallable (Maybe Integer -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> callFromEdh (fn (Just i)) (ArgsPack args kwargs) exit
      _ -> throwEdhTx UsageError "number type mismatch: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Int'
instance EdhCallable fn' => EdhCallable (Int -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> callFromEdh (fn $ fromInteger i) (ArgsPack args kwargs) exit
      _ -> throwEdhTx UsageError "number type mismatch: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Int'
instance EdhCallable fn' => EdhCallable (Maybe Int -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i ->
        callFromEdh (fn (Just $ fromInteger i)) (ArgsPack args kwargs) exit
      _ -> throwEdhTx UsageError "number type mismatch: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Bool'
instance EdhCallable fn' => EdhCallable (Bool -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBool !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Bool'
instance EdhCallable fn' => EdhCallable (Maybe Bool -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBool !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Blob'
instance EdhCallable fn' => EdhCallable (ByteString -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBlob !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Blob'
instance EdhCallable fn' => EdhCallable (Maybe ByteString -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhBlob !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Text'
instance EdhCallable fn' => EdhCallable (Text -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhString !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Text'
instance EdhCallable fn' => EdhCallable (Maybe Text -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhString !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Symbol'
instance EdhCallable fn' => EdhCallable (Symbol -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhSymbol !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Symbol'
instance EdhCallable fn' => EdhCallable (Maybe Symbol -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhSymbol !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'UUID'
instance EdhCallable fn' => EdhCallable (UUID.UUID -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhUUID !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'UUID'
instance EdhCallable fn' => EdhCallable (Maybe UUID.UUID -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhUUID !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhPair'
instance EdhCallable fn' => EdhCallable ((EdhValue, EdhValue) -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhPair !v1 !v2 -> callFromEdh (fn (v1, v2)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhPair'
instance EdhCallable fn' => EdhCallable (Maybe (EdhValue, EdhValue) -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhPair !v1 !v2 ->
      callFromEdh (fn (Just (v1, v2))) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Dict'
instance EdhCallable fn' => EdhCallable (Dict -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDict !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Dict'
instance EdhCallable fn' => EdhCallable (Maybe Dict -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhDict !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'List'
instance EdhCallable fn' => EdhCallable (List -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhList !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'List'
instance EdhCallable fn' => EdhCallable (Maybe List -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhList !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Object'
instance EdhCallable fn' => EdhCallable (Object -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhObject !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Object'
instance EdhCallable fn' => EdhCallable (Maybe Object -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhObject !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhOrd'
instance EdhCallable fn' => EdhCallable (Ordering -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhOrd !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhOrd'
instance EdhCallable fn' => EdhCallable (Maybe Ordering -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhOrd !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhSink'
instance EdhCallable fn' => EdhCallable (EdhSink -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhEvs !val' -> callFromEdh (fn val') (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhSink'
instance EdhCallable fn' => EdhCallable (Maybe EdhSink -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhEvs !val' -> callFromEdh (fn (Just val')) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhNamedValue'
instance EdhCallable fn' => EdhCallable ((AttrName, EdhValue) -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhNamedValue !name !value ->
      callFromEdh (fn (name, value)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhNamedValue'
instance EdhCallable fn' => EdhCallable (Maybe (AttrName, EdhValue) -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhNamedValue !name !value ->
      callFromEdh (fn (Just (name, value))) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhExpr'
instance EdhCallable fn' => EdhCallable (ExprDefi -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhExpr !expr _src ->
      callFromEdh (fn expr) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhExpr'
instance EdhCallable fn' => EdhCallable (Maybe ExprDefi -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhExpr !expr _src ->
      callFromEdh (fn (Just expr)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhExpr' with src
instance EdhCallable fn' => EdhCallable ((ExprDefi, Text) -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhExpr !expr !src ->
      callFromEdh (fn (expr, src)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhExpr' with src
instance EdhCallable fn' => EdhCallable (Maybe (ExprDefi, Text) -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhExpr !expr !src ->
      callFromEdh (fn (Just (expr, src))) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'PositionalArgs'
instance EdhCallable fn' => EdhCallable (PositionalArgs -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if odNull kwargs''
        then callFromEdh (fn (PositionalArgs args'')) (ArgsPack args kwargs) exit
        else throwEdhTx UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'PositionalArgs'
instance EdhCallable fn' => EdhCallable (Maybe PositionalArgs -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if odNull kwargs''
        then
          callFromEdh
            (fn (Just (PositionalArgs args'')))
            (ArgsPack args kwargs)
            exit
        else throwEdhTx UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'KeywordArgs'
instance EdhCallable fn' => EdhCallable (KeywordArgs -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if null args''
        then callFromEdh (fn (KeywordArgs kwargs'')) (ArgsPack args kwargs) exit
        else throwEdhTx UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'KeywordArgs'
instance EdhCallable fn' => EdhCallable (Maybe KeywordArgs -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if null args''
        then
          callFromEdh
            (fn (Just (KeywordArgs kwargs'')))
            (ArgsPack args kwargs)
            exit
        else throwEdhTx UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'PackedArgs'
instance EdhCallable fn' => EdhCallable (PackedArgs -> fn') where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack !apk ->
      callFromEdh (fn (PackedArgs apk)) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"
  callFromEdh _ _ _ = throwEdhTx UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'PackedArgs'
instance EdhCallable fn' => EdhCallable (Maybe PackedArgs -> fn') where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit =
    callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit = case val of
    EdhArgsPack !apk ->
      callFromEdh (fn (Just (PackedArgs apk))) (ArgsPack args kwargs) exit
    _ -> throwEdhTx UsageError "arg type mismatch: anonymous"

-- receive named arg taking 'EdhValue'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg EdhValue name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, kwargs') ->
        callFromEdh (fn (NamedEdhArg val)) (ArgsPack args kwargs') exit
      (Nothing, kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        (val : args') ->
          callFromEdh (fn (NamedEdhArg val)) (ArgsPack args' kwargs') exit
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhValue'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe EdhValue) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' ->
          callFromEdh
            (fn (NamedEdhArg (Just val)))
            (ArgsPack args' kwargs')
            exit
      (!maybeVal, !kwargs') ->
        callFromEdh (fn (NamedEdhArg maybeVal)) (ArgsPack args kwargs') exit
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Decimal'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg Decimal name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          callFromEdh (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Decimal for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            callFromEdh (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Decimal for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Decimal'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe Decimal) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          callFromEdh
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Decimal for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDecimal !val' ->
            callFromEdh
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Decimal for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Double'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg Double name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in callFromEdh (fn (NamedEdhArg d)) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Double for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in callFromEdh (fn (NamedEdhArg d)) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Double for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Double'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe Double) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in callFromEdh
                (fn (NamedEdhArg (Just d)))
                (ArgsPack args kwargs')
                exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Double for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in callFromEdh
                  (fn (NamedEdhArg (Just d)))
                  (ArgsPack args' kwargs')
                  exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Double for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Float'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg Float name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in callFromEdh (fn (NamedEdhArg d)) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Float for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in callFromEdh (fn (NamedEdhArg d)) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Float for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Float'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe Float) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in callFromEdh
                (fn (NamedEdhArg (Just d)))
                (ArgsPack args kwargs')
                exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Float for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in callFromEdh
                  (fn (NamedEdhArg (Just d)))
                  (ArgsPack args' kwargs')
                  exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Float for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Integer'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg Integer name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            callFromEdh (fn (NamedEdhArg i)) (ArgsPack args kwargs') exit
          _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Integer for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              callFromEdh (fn (NamedEdhArg i)) (ArgsPack args' kwargs') exit
            _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Integer for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Integer'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe Integer) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            callFromEdh (fn (NamedEdhArg (Just i))) (ArgsPack args kwargs') exit
          _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Integer for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              callFromEdh
                (fn (NamedEdhArg (Just i)))
                (ArgsPack args' kwargs')
                exit
            _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Integer for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Int'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg Int name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            callFromEdh
              (fn (NamedEdhArg $ fromInteger i))
              (ArgsPack args kwargs')
              exit
          _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Int for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              callFromEdh
                (fn (NamedEdhArg $ fromInteger i))
                (ArgsPack args' kwargs')
                exit
            _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Int for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Int'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe Int) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            callFromEdh
              (fn (NamedEdhArg (Just $ fromInteger i)))
              (ArgsPack args kwargs')
              exit
          _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Int for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              callFromEdh
                (fn (NamedEdhArg (Just $ fromInteger i)))
                (ArgsPack args' kwargs')
                exit
            _ -> throwEdhTx UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Int for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Bool'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg Bool name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBool !val' ->
          callFromEdh (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Bool for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhBool !val' ->
            callFromEdh (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Bool for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Bool'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe Bool) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBool !val' ->
          callFromEdh
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Bool for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhBool !val' ->
            callFromEdh
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Bool for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'ByteString'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg ByteString name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBlob !val' ->
          callFromEdh (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect ByteString for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhBlob !val' ->
            callFromEdh (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect ByteString for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'ByteString'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe ByteString) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBlob !val' ->
          callFromEdh
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect ByteString for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhBlob !val' ->
            callFromEdh
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect ByteString for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Text'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg Text name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhString !val' ->
          callFromEdh (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Text for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhString !val' ->
            callFromEdh (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Text for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Text'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe Text) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhString !val' ->
          callFromEdh
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Text for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhString !val' ->
            callFromEdh
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Text for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Symbol'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg Symbol name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSymbol !val' ->
          callFromEdh (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect symbol for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhSymbol !val' ->
            callFromEdh (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect symbol for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Symbol'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe Symbol) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSymbol !val' ->
          callFromEdh
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect symbol for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhSymbol !val' ->
            callFromEdh
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect symbol for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'UUID'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg UUID.UUID name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhUUID !val' ->
          callFromEdh (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect UUID for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhUUID !val' ->
            callFromEdh (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect UUID for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'UUID'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe UUID.UUID) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhUUID !val' ->
          callFromEdh
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect UUID for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhUUID !val' ->
            callFromEdh
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect UUID for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhPair'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (EdhValue, EdhValue) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhPair !v1 !v2 ->
          callFromEdh (fn (NamedEdhArg (v1, v2))) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect pair for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhPair !v1 !v2 ->
            callFromEdh
              (fn (NamedEdhArg (v1, v2)))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect pair for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhPair'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe (EdhValue, EdhValue)) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhPair !v1 !v2 ->
          callFromEdh
            (fn (NamedEdhArg (Just (v1, v2))))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect pair for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhPair !v1 !v2 ->
            callFromEdh
              (fn (NamedEdhArg (Just (v1, v2))))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect pair for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Dict'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg Dict name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDict !val' ->
          callFromEdh (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDict !val' ->
            callFromEdh (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Dict'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe Dict) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDict !val' ->
          callFromEdh
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhDict !val' ->
            callFromEdh
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'List'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg List name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhList !val' ->
          callFromEdh (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect list for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhList !val' ->
            callFromEdh (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect list for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'List'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe List) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhList !val' ->
          callFromEdh
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect list for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhList !val' ->
            callFromEdh
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect list for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Object'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg Object name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !val' ->
          callFromEdh (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect object for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhObject !val' ->
            callFromEdh (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect object for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Object'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe Object) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !val' ->
          callFromEdh
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect object for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhObject !val' ->
            callFromEdh
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect object for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Ordering'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg Ordering name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhOrd !val' ->
          callFromEdh (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Ordering for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhOrd !val' ->
            callFromEdh (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Ordering for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Ordering'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe Ordering) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhOrd !val' ->
          callFromEdh
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Ordering for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhOrd !val' ->
            callFromEdh
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Ordering for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhSink'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg EdhSink name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhEvs !val' ->
          callFromEdh (fn (NamedEdhArg val')) (ArgsPack args kwargs') exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect sink for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhEvs !val' ->
            callFromEdh (fn (NamedEdhArg val')) (ArgsPack args' kwargs') exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect sink for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhSink'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe EdhSink) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhEvs !val' ->
          callFromEdh
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect sink for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhEvs !val' ->
            callFromEdh
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect sink for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhNamedValue'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (AttrName, EdhValue) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhNamedValue !name !value ->
          callFromEdh
            (fn (NamedEdhArg (name, value)))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhNamedValue !name !value ->
            callFromEdh
              (fn (NamedEdhArg (name, value)))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhNamedValue'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe (AttrName, EdhValue)) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhNamedValue !name !value ->
          callFromEdh
            (fn (NamedEdhArg (Just (name, value))))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhNamedValue !name !value ->
            callFromEdh
              (fn (NamedEdhArg (Just (name, value))))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhExpr'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg ExprDefi name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr _src ->
          callFromEdh
            (fn (NamedEdhArg expr))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhExpr !expr _src ->
            callFromEdh
              (fn (NamedEdhArg expr))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhExpr'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe ExprDefi) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr _src ->
          callFromEdh
            (fn (NamedEdhArg (Just expr)))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhExpr !expr _src ->
            callFromEdh
              (fn (NamedEdhArg (Just expr)))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhExpr' with src
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (ExprDefi, Text) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr !src ->
          callFromEdh
            (fn (NamedEdhArg (expr, src)))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhExpr !expr !src ->
            callFromEdh
              (fn (NamedEdhArg (expr, src)))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhExpr' with src
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe (ExprDefi, Text)) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr !src ->
          callFromEdh
            (fn (NamedEdhArg (Just (expr, src))))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhExpr !expr !src ->
            callFromEdh
              (fn (NamedEdhArg (Just (expr, src))))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'PositionalArgs'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg PositionalArgs name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if odNull kwargs''
            then
              callFromEdh
                (fn (NamedEdhArg $ PositionalArgs args''))
                (ArgsPack args kwargs')
                exit
            else throwEdhTx UsageError $ "extraneous kwargs for: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect tuple for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if odNull kwargs''
              then
                callFromEdh
                  (fn (NamedEdhArg $ PositionalArgs args''))
                  (ArgsPack args' kwargs')
                  exit
              else throwEdhTx UsageError $ "extraneous kwargs for: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect tuple for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'PositionalArgs'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe PositionalArgs) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if odNull kwargs''
            then
              callFromEdh
                (fn (NamedEdhArg $ Just $ PositionalArgs args''))
                (ArgsPack args kwargs')
                exit
            else throwEdhTx UsageError $ "extraneous kwargs for: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect tuple for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if odNull kwargs''
              then
                callFromEdh
                  (fn (NamedEdhArg $ Just $ PositionalArgs args''))
                  (ArgsPack args' kwargs')
                  exit
              else throwEdhTx UsageError $ "extraneous kwargs for: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect tuple for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'KeywordArgs'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg KeywordArgs name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if null args''
            then
              callFromEdh
                (fn (NamedEdhArg $ KeywordArgs kwargs''))
                (ArgsPack args kwargs')
                exit
            else throwEdhTx UsageError $ "extraneous pos args for: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect kwargs for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if null args''
              then
                callFromEdh
                  (fn (NamedEdhArg $ KeywordArgs kwargs''))
                  (ArgsPack args' kwargs')
                  exit
              else throwEdhTx UsageError $ "extraneous pos args for: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect kwargs for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'KeywordArgs'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe KeywordArgs) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if null args''
            then
              callFromEdh
                (fn (NamedEdhArg $ Just $ KeywordArgs kwargs''))
                (ArgsPack args kwargs')
                exit
            else throwEdhTx UsageError $ "extraneous pos args for: " <> argName
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect kwargs for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if null args''
              then
                callFromEdh
                  (fn (NamedEdhArg $ Just $ KeywordArgs kwargs''))
                  (ArgsPack args' kwargs')
                  exit
              else throwEdhTx UsageError $ "extraneous pos args for: " <> argName
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect kwargs for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'PackedArgs'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg PackedArgs name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack !apk ->
          callFromEdh
            (fn (NamedEdhArg $ PackedArgs apk))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect apk for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhTx UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack !apk ->
            callFromEdh
              (fn (NamedEdhArg $ PackedArgs apk))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect apk for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'PackedArgs'
instance (KnownSymbol name, EdhCallable fn') => EdhCallable (NamedEdhArg (Maybe PackedArgs) name -> fn') where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack !apk ->
          callFromEdh
            (fn (NamedEdhArg (Just $ PackedArgs apk)))
            (ArgsPack args kwargs')
            exit
        _ ->
          throwEdhTx UsageError $
            "arg type mismatch: expect apk for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhArgsPack !apk ->
            callFromEdh
              (fn (NamedEdhArg (Just $ PackedArgs apk)))
              (ArgsPack args' kwargs')
              exit
          _ ->
            throwEdhTx UsageError $
              "arg type mismatch: expect apk for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- * general instances

-- receive anonymous arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (EdhAllocator fn', Typeable h) =>
  EdhAllocator (h -> fn')
  where
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit !ets = case val of
    EdhObject !obj -> (obj :) <$> readTVar (edh'obj'supers obj) >>= tryObjs
    _ -> throwEdh ets UsageError "arg type mismatch: anonymous"
    where
      tryObjs :: [Object] -> STM ()
      tryObjs [] = throwEdh ets UsageError "arg host type mismatch: anonymous"
      tryObjs (obj : rest) = case edh'obj'store obj of
        HostStore !hsd -> case fromDynamic hsd of
          Just (d :: h) ->
            runEdhTx ets $ allocEdhObj (fn d) (ArgsPack args kwargs) exit
          Nothing -> tryObjs rest
        _ -> tryObjs rest
  allocEdhObj _ _ _ !ets = throwEdh ets UsageError "missing anonymous arg"

-- receive optional anonymous arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (EdhAllocator fn', Typeable h) =>
  EdhAllocator (Maybe h -> fn')
  where
  allocEdhObj !fn (ArgsPack [] !kwargs) !exit !ets =
    runEdhTx ets $ allocEdhObj (fn Nothing) (ArgsPack [] kwargs) exit
  allocEdhObj !fn (ArgsPack (val : args) !kwargs) !exit !ets = case val of
    EdhObject !obj -> (obj :) <$> readTVar (edh'obj'supers obj) >>= tryObjs
    _ -> throwEdh ets UsageError "arg type mismatch: anonymous"
    where
      tryObjs :: [Object] -> STM ()
      tryObjs [] = throwEdh ets UsageError "arg host type mismatch: anonymous"
      tryObjs (obj : rest) = case edh'obj'store obj of
        HostStore !hsd -> case fromDynamic hsd of
          Just (d :: h) ->
            runEdhTx ets $ allocEdhObj (fn (Just d)) (ArgsPack args kwargs) exit
          Nothing -> tryObjs rest
        _ -> tryObjs rest

-- receive anonymous arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (EdhCallable fn', Typeable h) =>
  EdhCallable (h -> fn')
  where
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit !ets = case val of
    EdhObject !obj -> (obj :) <$> readTVar (edh'obj'supers obj) >>= tryObjs
    _ -> throwEdh ets UsageError "arg type mismatch: anonymous"
    where
      tryObjs :: [Object] -> STM ()
      tryObjs [] = throwEdh ets UsageError "arg host type mismatch: anonymous"
      tryObjs (obj : rest) = case edh'obj'store obj of
        HostStore !hsd -> case fromDynamic hsd of
          Just (d :: h) ->
            runEdhTx ets $ callFromEdh (fn d) (ArgsPack args kwargs) exit
          Nothing -> tryObjs rest
        _ -> tryObjs rest
  callFromEdh _ _ _ !ets = throwEdh ets UsageError "missing anonymous arg"

-- receive optional anonymous arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (EdhCallable fn', Typeable h) =>
  EdhCallable (Maybe h -> fn')
  where
  callFromEdh !fn (ArgsPack [] !kwargs) !exit !ets =
    runEdhTx ets $ callFromEdh (fn Nothing) (ArgsPack [] kwargs) exit
  callFromEdh !fn (ArgsPack (val : args) !kwargs) !exit !ets = case val of
    EdhObject !obj -> (obj :) <$> readTVar (edh'obj'supers obj) >>= tryObjs
    _ -> throwEdh ets UsageError "arg type mismatch: anonymous"
    where
      tryObjs :: [Object] -> STM ()
      tryObjs [] = throwEdh ets UsageError "arg host type mismatch: anonymous"
      tryObjs (obj : rest) = case edh'obj'store obj of
        HostStore !hsd -> case fromDynamic hsd of
          Just (d :: h) ->
            runEdhTx ets $ callFromEdh (fn (Just d)) (ArgsPack args kwargs) exit
          Nothing -> tryObjs rest
        _ -> tryObjs rest

-- receive named arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (KnownSymbol name, EdhAllocator fn', Typeable h) =>
  EdhAllocator (NamedEdhArg h name -> fn')
  where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit !ets =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !obj ->
          (obj :) <$> readTVar (edh'obj'supers obj) >>= goSearch args kwargs'
        _ ->
          throwEdh ets UsageError $
            "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
              <> " value for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdh ets UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhObject !obj ->
            (obj :) <$> readTVar (edh'obj'supers obj) >>= goSearch args' kwargs'
          _ ->
            throwEdh ets UsageError $
              "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
                <> " value for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      goSearch :: [EdhValue] -> KwArgs -> [Object] -> STM ()
      goSearch args' kwargs' = tryObjs
        where
          tryObjs :: [Object] -> STM ()
          tryObjs [] =
            throwEdh ets UsageError $ "arg host type mismatch: " <> argName
          tryObjs (obj : rest) = case edh'obj'store obj of
            HostStore !hsd -> case fromDynamic hsd of
              Just (d :: h) ->
                runEdhTx ets $
                  allocEdhObj (fn (NamedEdhArg d)) (ArgsPack args' kwargs') exit
              Nothing -> tryObjs rest
            _ -> tryObjs rest

-- receive named, optional arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (KnownSymbol name, EdhAllocator fn', Typeable h) =>
  EdhAllocator (NamedEdhArg (Maybe h) name -> fn')
  where
  allocEdhObj !fn (ArgsPack !args !kwargs) !exit !ets =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !obj ->
          (obj :) <$> readTVar (edh'obj'supers obj) >>= goSearch args kwargs'
        _ ->
          throwEdh ets UsageError $
            "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
              <> " value for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] ->
          runEdhTx ets $
            allocEdhObj (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhObject !obj ->
            (obj :) <$> readTVar (edh'obj'supers obj) >>= goSearch args' kwargs'
          _ ->
            throwEdh ets UsageError $
              "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
                <> " value for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      goSearch :: [EdhValue] -> KwArgs -> [Object] -> STM ()
      goSearch args' kwargs' = tryObjs
        where
          tryObjs :: [Object] -> STM ()
          tryObjs [] =
            throwEdh ets UsageError $ "arg host type mismatch: " <> argName
          tryObjs (obj : rest) = case edh'obj'store obj of
            HostStore !hsd -> case fromDynamic hsd of
              Just (d :: h) ->
                runEdhTx ets $
                  allocEdhObj
                    (fn (NamedEdhArg (Just d)))
                    (ArgsPack args' kwargs')
                    exit
              Nothing -> tryObjs rest
            _ -> tryObjs rest

-- receive named arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (KnownSymbol name, EdhCallable fn', Typeable h) =>
  EdhCallable (NamedEdhArg h name -> fn')
  where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit !ets =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !obj ->
          (obj :) <$> readTVar (edh'obj'supers obj) >>= goSearch args kwargs'
        _ ->
          throwEdh ets UsageError $
            "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
              <> " value for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdh ets UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhObject !obj ->
            (obj :) <$> readTVar (edh'obj'supers obj) >>= goSearch args' kwargs'
          _ ->
            throwEdh ets UsageError $
              "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
                <> " value for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      goSearch :: [EdhValue] -> KwArgs -> [Object] -> STM ()
      goSearch args' kwargs' = tryObjs
        where
          tryObjs :: [Object] -> STM ()
          tryObjs [] =
            throwEdh ets UsageError $ "arg host type mismatch: " <> argName
          tryObjs (obj : rest) = case edh'obj'store obj of
            HostStore !hsd -> case fromDynamic hsd of
              Just (d :: h) ->
                runEdhTx ets $
                  callFromEdh (fn (NamedEdhArg d)) (ArgsPack args' kwargs') exit
              Nothing -> tryObjs rest
            _ -> tryObjs rest

-- receive named, optional arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (KnownSymbol name, EdhCallable fn', Typeable h) =>
  EdhCallable (NamedEdhArg (Maybe h) name -> fn')
  where
  callFromEdh !fn (ArgsPack !args !kwargs) !exit !ets =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !obj ->
          (obj :) <$> readTVar (edh'obj'supers obj) >>= goSearch args kwargs'
        _ ->
          throwEdh ets UsageError $
            "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
              <> " value for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] ->
          runEdhTx ets $
            callFromEdh (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs') exit
        val : args' -> case val of
          EdhObject !obj ->
            (obj :) <$> readTVar (edh'obj'supers obj) >>= goSearch args' kwargs'
          _ ->
            throwEdh ets UsageError $
              "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
                <> " value for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      goSearch :: [EdhValue] -> KwArgs -> [Object] -> STM ()
      goSearch args' kwargs' = tryObjs
        where
          tryObjs :: [Object] -> STM ()
          tryObjs [] =
            throwEdh ets UsageError $ "arg host type mismatch: " <> argName
          tryObjs (obj : rest) = case edh'obj'store obj of
            HostStore !hsd -> case fromDynamic hsd of
              Just (d :: h) ->
                runEdhTx ets $
                  callFromEdh
                    (fn (NamedEdhArg (Just d)))
                    (ArgsPack args' kwargs')
                    exit
              Nothing -> tryObjs rest
            _ -> tryObjs rest
