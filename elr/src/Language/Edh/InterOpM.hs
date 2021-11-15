module Language.Edh.InterOpM where

import Data.ByteString (ByteString)
import Data.Dynamic
import Data.Lossless.Decimal (Decimal)
import qualified Data.Lossless.Decimal as D
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.UUID as UUID
import Data.Unique
import GHC.TypeLits (KnownSymbol, symbolVal)
import Language.Edh.Args
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.Monad
import Language.Edh.RtTypes
import Type.Reflection
import Prelude

-- * utilities

wrapEdhProc ::
  EdhCallableM fn => fn -> (ArgsPack -> Edh EdhValue, ArgsReceiver)
wrapEdhProc !fn =
  -- TODO derive arg receivers (procedure signature)
  (callFromEdhM fn, NullaryReceiver)

mkEdhProc' ::
  EdhCallableM fn =>
  (ProcDefi -> EdhProcDefi) ->
  AttrName ->
  fn ->
  Edh EdhValue
mkEdhProc' !vc !nm !fn = mkEdhProc vc nm $ wrapEdhProc fn

mkEdhProperty ::
  AttrName ->
  Edh EdhValue ->
  Maybe (Maybe EdhValue -> Edh EdhValue) ->
  Edh EdhValue
mkEdhProperty !nm !getterProc !maybeSetterProc = do
  !ets <- edhThreadState
  let !scope = contextScope $ edh'context ets
  getter <- do
    u <- newUniqueEdh
    return $
      ProcDefi
        { edh'procedure'ident = u,
          edh'procedure'name = AttrByName nm,
          edh'procedure'lexi = scope,
          edh'procedure'doc = NoDocCmt,
          edh'procedure'decl = HostDecl $
            \apk -> unEdh (callFromEdhM getterProc apk) rptEdhNotApplicable
        }
  setter <- case maybeSetterProc of
    Nothing -> return Nothing
    Just !setterProc -> do
      u <- newUniqueEdh
      return $
        Just $
          ProcDefi
            { edh'procedure'ident = u,
              edh'procedure'name = AttrByName nm,
              edh'procedure'lexi = scope,
              edh'procedure'doc = NoDocCmt,
              edh'procedure'decl = HostDecl $
                \apk -> unEdh (callFromEdhM setterProc apk) rptEdhNotApplicable
            }
  return $ EdhProcedure (EdhDescriptor getter setter) Nothing

-- | Class for a procedure implemented in the host language (which is Haskell)
-- that can be called from Edh code.
--
-- Note the top frame of the call stack from thread state is the one for the
-- callee, that scope should have mounted the caller's scope entity, not a new
-- entity in contrast to when an Edh procedure as the callee.
class EdhCallableM fn where
  callFromEdhM :: fn -> ArgsPack -> Edh EdhValue

-- nullary base case
instance EdhCallableM (Edh EdhValue) where
  callFromEdhM !fn apk@(ArgsPack !args !kwargs) =
    if null args && odNull kwargs
      then fn
      else
        edhValueReprM (EdhArgsPack apk) >>= \ !badRepr ->
          throwEdhM UsageError $ "extraneous arguments: " <> badRepr

-- repack rest-positional-args
instance EdhCallableM fn' => EdhCallableM ([EdhValue] -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    callFromEdhM (fn args) (ArgsPack [] kwargs)

instance EdhCallableM fn' => EdhCallableM (NamedEdhArg [EdhValue] name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    callFromEdhM (fn (NamedEdhArg args)) (ArgsPack [] kwargs)

-- repack rest-keyword-args
instance EdhCallableM fn' => EdhCallableM (KwArgs -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    callFromEdhM (fn kwargs) (ArgsPack args odEmpty)

instance EdhCallableM fn' => EdhCallableM (NamedEdhArg KwArgs name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    callFromEdhM (fn (NamedEdhArg kwargs)) (ArgsPack args odEmpty)

-- repack rest-pack-args
--
-- note it'll cause runtime error if @fn'@ takes further args
-- todo detect that case and report static errors?
instance EdhCallableM fn' => EdhCallableM (ArgsPack -> fn') where
  callFromEdhM !fn !apk = callFromEdhM (fn apk) (ArgsPack [] odEmpty)

instance EdhCallableM fn' => EdhCallableM (NamedEdhArg ArgsPack name -> fn') where
  callFromEdhM !fn !apk =
    callFromEdhM (fn (NamedEdhArg apk)) (ArgsPack [] odEmpty)

-- receive anonymous arg taking 'EdhValue'
instance EdhCallableM fn' => EdhCallableM (EdhValue -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) =
    callFromEdhM (fn val) (ArgsPack args kwargs)
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhValue'
instance EdhCallableM fn' => EdhCallableM (Maybe EdhValue -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) =
    callFromEdhM (fn (Just val)) (ArgsPack args kwargs)

-- receive anonymous arg taking a quantity value,
-- converted in to the designated uom
instance
  (EdhCallableM fn', KnownSymbol uom) =>
  EdhCallableM (QtyAsIn uom -> fn')
  where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhQty qty@(Quantity !q !u) ->
      if uomDefiIdent u == uomIdent
        then callFromEdhM (fn $ Qty q) (ArgsPack args kwargs)
        else mEdh $ \exit ->
          resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
            unifyToUnit
              uom
              (Right qty)
              ( \q' ets ->
                  runEdh
                    ets
                    (callFromEdhM (fn $ Qty q') (ArgsPack args kwargs))
                    exit
              )
              $ throwEdhTx UsageError $
                "arg uom mismatch: expect quantity in [" <> uomIdent
                  <> "] but given "
                  <> uomDefiIdent u
    EdhDecimal !d -> mEdh $ \exit ->
      resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
        unifyToUnit
          uom
          (Left d)
          ( \q' ets ->
              runEdh
                ets
                (callFromEdhM (fn $ Qty q') (ArgsPack args kwargs))
                exit
          )
          $ throwEdhTx UsageError $
            "arg uom mismatch: expect quantity in [" <> uomIdent
              <> "] but given a pure number"
    _ ->
      throwEdhM UsageError $
        "arg type mismatch: expect quantity in [" <> uomIdent
          <> "] but given "
          <> edhTypeNameOf val
    where
      !uomIdent = T.pack $ symbolVal (Proxy :: Proxy uom)
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking a quantity value,
-- converted in to the designated uom
instance
  (EdhCallableM fn', KnownSymbol uom) =>
  EdhCallableM (Maybe (QtyAsIn uom) -> fn')
  where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhQty qty@(Quantity !q !u) ->
      if uomDefiIdent u == uomIdent
        then callFromEdhM (fn $ Just $ Qty q) (ArgsPack args kwargs)
        else mEdh $ \exit ->
          resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
            unifyToUnit
              uom
              (Right qty)
              ( \q' ets ->
                  runEdh
                    ets
                    (callFromEdhM (fn $ Just $ Qty q') (ArgsPack args kwargs))
                    exit
              )
              $ throwEdhTx UsageError $
                "arg uom mismatch: expect quantity in [" <> uomIdent
                  <> "] but given "
                  <> uomDefiIdent u
    EdhDecimal !d -> mEdh $ \exit ->
      resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
        unifyToUnit
          uom
          (Left d)
          ( \q' ets ->
              runEdh
                ets
                (callFromEdhM (fn $ Just $ Qty q') (ArgsPack args kwargs))
                exit
          )
          $ throwEdhTx UsageError $
            "arg uom mismatch: expect quantity in [" <> uomIdent
              <> "] but given a pure number"
    _ ->
      throwEdhM UsageError $
        "arg type mismatch: expect quantity in [" <> uomIdent
          <> "] but given "
          <> edhTypeNameOf val
    where
      !uomIdent = T.pack $ symbolVal (Proxy :: Proxy uom)

-- receive anonymous arg taking 'Decimal'
instance EdhCallableM fn' => EdhCallableM (Decimal -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' -> callFromEdhM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Decimal'
instance EdhCallableM fn' => EdhCallableM (Maybe Decimal -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' ->
      callFromEdhM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Double'
instance EdhCallableM fn' => EdhCallableM (Double -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in callFromEdhM (fn d) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Double'
instance EdhCallableM fn' => EdhCallableM (Maybe Double -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in callFromEdhM (fn (Just d)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Float'
instance EdhCallableM fn' => EdhCallableM (Float -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in callFromEdhM (fn d) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Float'
instance EdhCallableM fn' => EdhCallableM (Maybe Float -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in callFromEdhM (fn (Just d)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Integer'
instance EdhCallableM fn' => EdhCallableM (Integer -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> callFromEdhM (fn i) (ArgsPack args kwargs)
      _ -> throwEdhM UsageError "number type mismatch: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Integer'
instance EdhCallableM fn' => EdhCallableM (Maybe Integer -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> callFromEdhM (fn (Just i)) (ArgsPack args kwargs)
      _ -> throwEdhM UsageError "number type mismatch: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Int'
instance EdhCallableM fn' => EdhCallableM (Int -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> callFromEdhM (fn $ fromInteger i) (ArgsPack args kwargs)
      _ -> throwEdhM UsageError "number type mismatch: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Int'
instance EdhCallableM fn' => EdhCallableM (Maybe Int -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i ->
        callFromEdhM (fn (Just $ fromInteger i)) (ArgsPack args kwargs)
      _ -> throwEdhM UsageError "number type mismatch: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Bool'
instance EdhCallableM fn' => EdhCallableM (Bool -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhBool !val' -> callFromEdhM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Bool'
instance EdhCallableM fn' => EdhCallableM (Maybe Bool -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhBool !val' -> callFromEdhM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Blob'
instance EdhCallableM fn' => EdhCallableM (ByteString -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhBlob !val' -> callFromEdhM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Blob'
instance EdhCallableM fn' => EdhCallableM (Maybe ByteString -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhBlob !val' -> callFromEdhM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Text'
instance EdhCallableM fn' => EdhCallableM (Text -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhString !val' -> callFromEdhM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Text'
instance EdhCallableM fn' => EdhCallableM (Maybe Text -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhString !val' -> callFromEdhM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Symbol'
instance EdhCallableM fn' => EdhCallableM (Symbol -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhSymbol !val' -> callFromEdhM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Symbol'
instance EdhCallableM fn' => EdhCallableM (Maybe Symbol -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhSymbol !val' -> callFromEdhM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'UUID'
instance EdhCallableM fn' => EdhCallableM (UUID.UUID -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhUUID !val' -> callFromEdhM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'UUID'
instance EdhCallableM fn' => EdhCallableM (Maybe UUID.UUID -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhUUID !val' -> callFromEdhM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhPair'
instance EdhCallableM fn' => EdhCallableM ((EdhValue, EdhValue) -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhPair !v1 !v2 -> callFromEdhM (fn (v1, v2)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhPair'
instance EdhCallableM fn' => EdhCallableM (Maybe (EdhValue, EdhValue) -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhPair !v1 !v2 ->
      callFromEdhM (fn (Just (v1, v2))) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Dict'
instance EdhCallableM fn' => EdhCallableM (Dict -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDict !val' -> callFromEdhM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Dict'
instance EdhCallableM fn' => EdhCallableM (Maybe Dict -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDict !val' -> callFromEdhM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'List'
instance EdhCallableM fn' => EdhCallableM (List -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhList !val' -> callFromEdhM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'List'
instance EdhCallableM fn' => EdhCallableM (Maybe List -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhList !val' -> callFromEdhM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Object'
instance EdhCallableM fn' => EdhCallableM (Object -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhObject !val' -> callFromEdhM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Object'
instance EdhCallableM fn' => EdhCallableM (Maybe Object -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhObject !val' -> callFromEdhM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhOrd'
instance EdhCallableM fn' => EdhCallableM (Ordering -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhOrd !val' -> callFromEdhM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhOrd'
instance EdhCallableM fn' => EdhCallableM (Maybe Ordering -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhOrd !val' -> callFromEdhM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Sink'
instance EdhCallableM fn' => EdhCallableM (Sink -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhSink !val' -> callFromEdhM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Sink'
instance EdhCallableM fn' => EdhCallableM (Maybe Sink -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhSink !val' -> callFromEdhM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhNamedValue'
instance EdhCallableM fn' => EdhCallableM ((AttrName, EdhValue) -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhNamedValue !name !value ->
      callFromEdhM (fn (name, value)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhNamedValue'
instance EdhCallableM fn' => EdhCallableM (Maybe (AttrName, EdhValue) -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhNamedValue !name !value ->
      callFromEdhM (fn (Just (name, value))) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'ExprDefi'
instance EdhCallableM fn' => EdhCallableM (ExprDefi -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhExpr !expr _src ->
      callFromEdhM (fn expr) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'ExprDefi'
instance EdhCallableM fn' => EdhCallableM (Maybe ExprDefi -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhExpr !expr _src ->
      callFromEdhM (fn (Just expr)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'ExprDefi' with src
instance EdhCallableM fn' => EdhCallableM ((ExprDefi, Text) -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhExpr !expr !src ->
      callFromEdhM (fn (expr, src)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'ExprDefi' with src
instance EdhCallableM fn' => EdhCallableM (Maybe (ExprDefi, Text) -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhExpr !expr !src ->
      callFromEdhM (fn (Just (expr, src))) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'PositionalArgs'
instance EdhCallableM fn' => EdhCallableM (PositionalArgs -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if odNull kwargs''
        then callFromEdhM (fn (PositionalArgs args'')) (ArgsPack args kwargs)
        else throwEdhM UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'PositionalArgs'
instance EdhCallableM fn' => EdhCallableM (Maybe PositionalArgs -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if odNull kwargs''
        then
          callFromEdhM
            (fn (Just (PositionalArgs args'')))
            (ArgsPack args kwargs)
        else throwEdhM UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'KeywordArgs'
instance EdhCallableM fn' => EdhCallableM (KeywordArgs -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if null args''
        then callFromEdhM (fn (KeywordArgs kwargs'')) (ArgsPack args kwargs)
        else throwEdhM UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'KeywordArgs'
instance EdhCallableM fn' => EdhCallableM (Maybe KeywordArgs -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if null args''
        then
          callFromEdhM
            (fn (Just (KeywordArgs kwargs'')))
            (ArgsPack args kwargs)
        else throwEdhM UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'PackedArgs'
instance EdhCallableM fn' => EdhCallableM (PackedArgs -> fn') where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack !apk ->
      callFromEdhM (fn (PackedArgs apk)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'PackedArgs'
instance EdhCallableM fn' => EdhCallableM (Maybe PackedArgs -> fn') where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack !apk ->
      callFromEdhM (fn (Just (PackedArgs apk))) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive named arg taking 'EdhValue'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg EdhValue name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, kwargs') ->
        callFromEdhM (fn (NamedEdhArg val)) (ArgsPack args kwargs')
      (Nothing, kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        (val : args') ->
          callFromEdhM (fn (NamedEdhArg val)) (ArgsPack args' kwargs')
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhValue'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe EdhValue) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val)))
            (ArgsPack args' kwargs')
      (!maybeVal, !kwargs') ->
        callFromEdhM (fn (NamedEdhArg maybeVal)) (ArgsPack args kwargs')
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking a quantity value,
-- converted in to the designated uom
instance
  (KnownSymbol name, KnownSymbol uom, EdhCallableM fn') =>
  EdhCallableM (NamedEdhArg (QtyAsIn uom) name -> fn')
  where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhQty qty@(Quantity !q !u) ->
          if uomDefiIdent u == uomIdent
            then
              callFromEdhM
                (fn (NamedEdhArg (Qty q)))
                (ArgsPack args kwargs')
            else mEdh $ \exit ->
              resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
                unifyToUnit
                  uom
                  (Right qty)
                  ( \q' ets ->
                      runEdh
                        ets
                        ( callFromEdhM
                            (fn (NamedEdhArg (Qty q')))
                            (ArgsPack args kwargs')
                        )
                        exit
                  )
                  $ throwEdhTx UsageError $
                    "arg uom mismatch: expect quantity in [" <> uomIdent
                      <> "] for "
                      <> argName
                      <> " but given "
                      <> uomDefiIdent u
        EdhDecimal !d -> mEdh $ \exit ->
          resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
            unifyToUnit
              uom
              (Left d)
              ( \q' ets ->
                  runEdh
                    ets
                    ( callFromEdhM
                        (fn (NamedEdhArg (Qty q')))
                        (ArgsPack args kwargs')
                    )
                    exit
              )
              $ throwEdhTx UsageError $
                "arg uom mismatch: expect quantity in [" <> uomIdent
                  <> "] for "
                  <> argName
                  <> " but given a pure number"
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect quantity in [" <> uomIdent <> "] for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhQty qty@(Quantity !q !u) ->
            if uomDefiIdent u == uomIdent
              then
                callFromEdhM
                  (fn (NamedEdhArg (Qty q)))
                  (ArgsPack args' kwargs')
              else mEdh $ \exit ->
                resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
                  unifyToUnit
                    uom
                    (Right qty)
                    ( \q' ets ->
                        runEdh
                          ets
                          ( callFromEdhM
                              (fn (NamedEdhArg (Qty q')))
                              (ArgsPack args' kwargs')
                          )
                          exit
                    )
                    $ throwEdhTx UsageError $
                      "arg uom mismatch: expect quantity in [" <> uomIdent
                        <> "] for "
                        <> argName
                        <> " but given "
                        <> uomDefiIdent u
          EdhDecimal !d -> mEdh $ \exit ->
            resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
              unifyToUnit
                uom
                (Left d)
                ( \q' ets ->
                    runEdh
                      ets
                      ( callFromEdhM
                          (fn (NamedEdhArg (Qty q')))
                          (ArgsPack args' kwargs')
                      )
                      exit
                )
                $ throwEdhTx UsageError $
                  "arg uom mismatch: expect quantity in [" <> uomIdent
                    <> "] for "
                    <> argName
                    <> " but given a pure number"
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect quantity in [" <> uomIdent <> "] for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      !uomIdent = T.pack $ symbolVal (Proxy :: Proxy uom)

-- receive named, optional arg taking a quantity value,
-- converted in to the designated uom
instance
  (KnownSymbol name, KnownSymbol uom, EdhCallableM fn') =>
  EdhCallableM (NamedEdhArg (Maybe (QtyAsIn uom)) name -> fn')
  where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhQty qty@(Quantity !q !u) ->
          if uomDefiIdent u == uomIdent
            then
              callFromEdhM
                (fn (NamedEdhArg $ Just $ Qty q))
                (ArgsPack args kwargs')
            else mEdh $ \exit ->
              resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
                unifyToUnit
                  uom
                  (Right qty)
                  ( \q' ets ->
                      runEdh
                        ets
                        ( callFromEdhM
                            (fn (NamedEdhArg $ Just $ Qty q'))
                            (ArgsPack args kwargs')
                        )
                        exit
                  )
                  $ throwEdhTx UsageError $
                    "arg uom mismatch: expect quantity in [" <> uomIdent
                      <> "] for "
                      <> argName
                      <> " but given "
                      <> uomDefiIdent u
        EdhDecimal !d -> mEdh $ \exit ->
          resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
            unifyToUnit
              uom
              (Left d)
              ( \q' ets ->
                  runEdh
                    ets
                    ( callFromEdhM
                        (fn (NamedEdhArg $ Just $ Qty q'))
                        (ArgsPack args kwargs')
                    )
                    exit
              )
              $ throwEdhTx UsageError $
                "arg uom mismatch: expect quantity in [" <> uomIdent
                  <> "] for "
                  <> argName
                  <> " but given a pure number"
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect quantity in [" <> uomIdent <> "] for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhQty qty@(Quantity !q !u) ->
            if uomDefiIdent u == uomIdent
              then
                callFromEdhM
                  (fn (NamedEdhArg $ Just $ Qty q))
                  (ArgsPack args' kwargs')
              else mEdh $ \exit ->
                resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
                  unifyToUnit
                    uom
                    (Right qty)
                    ( \q' ets ->
                        runEdh
                          ets
                          ( callFromEdhM
                              (fn (NamedEdhArg $ Just $ Qty q'))
                              (ArgsPack args' kwargs')
                          )
                          exit
                    )
                    $ throwEdhTx UsageError $
                      "arg uom mismatch: expect quantity in [" <> uomIdent
                        <> "] for "
                        <> argName
                        <> " but given "
                        <> uomDefiIdent u
          EdhDecimal !d -> mEdh $ \exit ->
            resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
              unifyToUnit
                uom
                (Left d)
                ( \q' ets ->
                    runEdh
                      ets
                      ( callFromEdhM
                          (fn (NamedEdhArg $ Just $ Qty q'))
                          (ArgsPack args' kwargs')
                      )
                      exit
                )
                $ throwEdhTx UsageError $
                  "arg uom mismatch: expect quantity in [" <> uomIdent
                    <> "] for "
                    <> argName
                    <> " but given a pure number"
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect quantity in [" <> uomIdent <> "] for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
            where
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      !uomIdent = T.pack $ symbolVal (Proxy :: Proxy uom)

-- receive named arg taking 'Decimal'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Decimal name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Decimal for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Decimal for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Decimal'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Decimal) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Decimal for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDecimal !val' ->
            callFromEdhM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Decimal for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Double'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Double name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in callFromEdhM (fn (NamedEdhArg d)) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Double for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in callFromEdhM (fn (NamedEdhArg d)) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Double for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Double'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Double) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in callFromEdhM
                (fn (NamedEdhArg (Just d)))
                (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Double for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in callFromEdhM
                  (fn (NamedEdhArg (Just d)))
                  (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Double for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Float'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Float name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in callFromEdhM (fn (NamedEdhArg d)) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Float for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in callFromEdhM (fn (NamedEdhArg d)) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Float for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Float'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Float) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in callFromEdhM
                (fn (NamedEdhArg (Just d)))
                (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Float for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in callFromEdhM
                  (fn (NamedEdhArg (Just d)))
                  (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Float for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Integer'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Integer name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            callFromEdhM (fn (NamedEdhArg i)) (ArgsPack args kwargs')
          _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Integer for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              callFromEdhM (fn (NamedEdhArg i)) (ArgsPack args' kwargs')
            _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Integer for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Integer'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Integer) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            callFromEdhM (fn (NamedEdhArg (Just i))) (ArgsPack args kwargs')
          _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Integer for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              callFromEdhM
                (fn (NamedEdhArg (Just i)))
                (ArgsPack args' kwargs')
            _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Integer for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Int'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Int name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            callFromEdhM
              (fn (NamedEdhArg $ fromInteger i))
              (ArgsPack args kwargs')
          _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Int for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              callFromEdhM
                (fn (NamedEdhArg $ fromInteger i))
                (ArgsPack args' kwargs')
            _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Int for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Int'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Int) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            callFromEdhM
              (fn (NamedEdhArg (Just $ fromInteger i)))
              (ArgsPack args kwargs')
          _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Int for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              callFromEdhM
                (fn (NamedEdhArg (Just $ fromInteger i)))
                (ArgsPack args' kwargs')
            _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Int for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Bool'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Bool name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBool !val' ->
          callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Bool for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhBool !val' ->
            callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Bool for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Bool'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Bool) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBool !val' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Bool for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhBool !val' ->
            callFromEdhM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Bool for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'ByteString'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg ByteString name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBlob !val' ->
          callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect ByteString for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhBlob !val' ->
            callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect ByteString for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'ByteString'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe ByteString) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBlob !val' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect ByteString for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhBlob !val' ->
            callFromEdhM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect ByteString for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Text'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Text name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhString !val' ->
          callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Text for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhString !val' ->
            callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Text for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Text'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Text) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhString !val' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Text for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhString !val' ->
            callFromEdhM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Text for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Symbol'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Symbol name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSymbol !val' ->
          callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect symbol for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhSymbol !val' ->
            callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect symbol for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Symbol'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Symbol) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSymbol !val' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect symbol for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhSymbol !val' ->
            callFromEdhM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect symbol for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'UUID'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg UUID.UUID name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhUUID !val' ->
          callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect UUID for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhUUID !val' ->
            callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect UUID for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'UUID'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe UUID.UUID) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhUUID !val' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect UUID for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhUUID !val' ->
            callFromEdhM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect UUID for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhPair'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (EdhValue, EdhValue) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhPair !v1 !v2 ->
          callFromEdhM (fn (NamedEdhArg (v1, v2))) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect pair for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhPair !v1 !v2 ->
            callFromEdhM
              (fn (NamedEdhArg (v1, v2)))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect pair for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhPair'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe (EdhValue, EdhValue)) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhPair !v1 !v2 ->
          callFromEdhM
            (fn (NamedEdhArg (Just (v1, v2))))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect pair for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhPair !v1 !v2 ->
            callFromEdhM
              (fn (NamedEdhArg (Just (v1, v2))))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect pair for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Dict'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Dict name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDict !val' ->
          callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDict !val' ->
            callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Dict'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Dict) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDict !val' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDict !val' ->
            callFromEdhM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'List'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg List name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhList !val' ->
          callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect list for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhList !val' ->
            callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect list for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'List'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe List) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhList !val' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect list for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhList !val' ->
            callFromEdhM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect list for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Object'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Object name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !val' ->
          callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect object for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhObject !val' ->
            callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect object for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Object'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Object) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !val' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect object for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhObject !val' ->
            callFromEdhM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect object for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Ordering'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Ordering name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhOrd !val' ->
          callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Ordering for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhOrd !val' ->
            callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Ordering for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Ordering'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Ordering) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhOrd !val' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Ordering for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhOrd !val' ->
            callFromEdhM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Ordering for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Sink'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg Sink name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSink !val' ->
          callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect sink for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhSink !val' ->
            callFromEdhM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect sink for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Sink'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe Sink) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSink !val' ->
          callFromEdhM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect sink for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhSink !val' ->
            callFromEdhM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect sink for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhNamedValue'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (AttrName, EdhValue) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhNamedValue !name !value ->
          callFromEdhM
            (fn (NamedEdhArg (name, value)))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhNamedValue !name !value ->
            callFromEdhM
              (fn (NamedEdhArg (name, value)))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhNamedValue'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe (AttrName, EdhValue)) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhNamedValue !name !value ->
          callFromEdhM
            (fn (NamedEdhArg (Just (name, value))))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhNamedValue !name !value ->
            callFromEdhM
              (fn (NamedEdhArg (Just (name, value))))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'ExprDefi'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg ExprDefi name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr _src ->
          callFromEdhM
            (fn (NamedEdhArg expr))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhExpr !expr _src ->
            callFromEdhM
              (fn (NamedEdhArg expr))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'ExprDefi'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe ExprDefi) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr _src ->
          callFromEdhM
            (fn (NamedEdhArg (Just expr)))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhExpr !expr _src ->
            callFromEdhM
              (fn (NamedEdhArg (Just expr)))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'ExprDefi' with src
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (ExprDefi, Text) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr !src ->
          callFromEdhM
            (fn (NamedEdhArg (expr, src)))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhExpr !expr !src ->
            callFromEdhM
              (fn (NamedEdhArg (expr, src)))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'ExprDefi' with src
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe (ExprDefi, Text)) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr !src ->
          callFromEdhM
            (fn (NamedEdhArg (Just (expr, src))))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhExpr !expr !src ->
            callFromEdhM
              (fn (NamedEdhArg (Just (expr, src))))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'PositionalArgs'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg PositionalArgs name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if odNull kwargs''
            then
              callFromEdhM
                (fn (NamedEdhArg $ PositionalArgs args''))
                (ArgsPack args kwargs')
            else throwEdhM UsageError $ "extraneous kwargs for: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect tuple for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if odNull kwargs''
              then
                callFromEdhM
                  (fn (NamedEdhArg $ PositionalArgs args''))
                  (ArgsPack args' kwargs')
              else throwEdhM UsageError $ "extraneous kwargs for: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect tuple for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'PositionalArgs'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe PositionalArgs) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if odNull kwargs''
            then
              callFromEdhM
                (fn (NamedEdhArg $ Just $ PositionalArgs args''))
                (ArgsPack args kwargs')
            else throwEdhM UsageError $ "extraneous kwargs for: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect tuple for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if odNull kwargs''
              then
                callFromEdhM
                  (fn (NamedEdhArg $ Just $ PositionalArgs args''))
                  (ArgsPack args' kwargs')
              else throwEdhM UsageError $ "extraneous kwargs for: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect tuple for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'KeywordArgs'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg KeywordArgs name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if null args''
            then
              callFromEdhM
                (fn (NamedEdhArg $ KeywordArgs kwargs''))
                (ArgsPack args kwargs')
            else throwEdhM UsageError $ "extraneous pos args for: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect kwargs for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if null args''
              then
                callFromEdhM
                  (fn (NamedEdhArg $ KeywordArgs kwargs''))
                  (ArgsPack args' kwargs')
              else throwEdhM UsageError $ "extraneous pos args for: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect kwargs for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'KeywordArgs'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe KeywordArgs) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if null args''
            then
              callFromEdhM
                (fn (NamedEdhArg $ Just $ KeywordArgs kwargs''))
                (ArgsPack args kwargs')
            else throwEdhM UsageError $ "extraneous pos args for: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect kwargs for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if null args''
              then
                callFromEdhM
                  (fn (NamedEdhArg $ Just $ KeywordArgs kwargs''))
                  (ArgsPack args' kwargs')
              else throwEdhM UsageError $ "extraneous pos args for: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect kwargs for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'PackedArgs'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg PackedArgs name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack !apk ->
          callFromEdhM
            (fn (NamedEdhArg $ PackedArgs apk))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect apk for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack !apk ->
            callFromEdhM
              (fn (NamedEdhArg $ PackedArgs apk))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect apk for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'PackedArgs'
instance (KnownSymbol name, EdhCallableM fn') => EdhCallableM (NamedEdhArg (Maybe PackedArgs) name -> fn') where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack !apk ->
          callFromEdhM
            (fn (NamedEdhArg (Just $ PackedArgs apk)))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect apk for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhArgsPack !apk ->
            callFromEdhM
              (fn (NamedEdhArg (Just $ PackedArgs apk)))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect apk for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- * general instances

{- HLINT ignore "Redundant <$>" -}

-- receive anonymous arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (EdhCallableM fn', Typeable h) =>
  EdhCallableM (h -> fn')
  where
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhObject !obj -> (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= tryObjs
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
    where
      tryObjs :: [Object] -> Edh EdhValue
      tryObjs [] = throwEdhM UsageError "arg host type mismatch: anonymous"
      tryObjs (obj : rest) = case edh'obj'store obj of
        HostStore !hsd -> case fromDynamic hsd of
          Just (d :: h) ->
            callFromEdhM (fn d) (ArgsPack args kwargs)
          Nothing -> tryObjs rest
        _ -> tryObjs rest
  callFromEdhM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (EdhCallableM fn', Typeable h) =>
  EdhCallableM (Maybe h -> fn')
  where
  callFromEdhM !fn (ArgsPack [] !kwargs) =
    callFromEdhM (fn Nothing) (ArgsPack [] kwargs)
  callFromEdhM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhObject !obj -> (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= tryObjs
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
    where
      tryObjs :: [Object] -> Edh EdhValue
      tryObjs [] = throwEdhM UsageError "arg host type mismatch: anonymous"
      tryObjs (obj : rest) = case edh'obj'store obj of
        HostStore !hsd -> case fromDynamic hsd of
          Just (d :: h) ->
            callFromEdhM (fn (Just d)) (ArgsPack args kwargs)
          Nothing -> tryObjs rest
        _ -> tryObjs rest

-- receive named arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (KnownSymbol name, EdhCallableM fn', Typeable h) =>
  EdhCallableM (NamedEdhArg h name -> fn')
  where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !obj ->
          (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= goSearch args kwargs'
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
              <> " value for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhObject !obj ->
            (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= goSearch args' kwargs'
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
                <> " value for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      goSearch :: [EdhValue] -> KwArgs -> [Object] -> Edh EdhValue
      goSearch args' kwargs' = tryObjs
        where
          tryObjs :: [Object] -> Edh EdhValue
          tryObjs [] =
            throwEdhM UsageError $ "arg host type mismatch: " <> argName
          tryObjs (obj : rest) = case edh'obj'store obj of
            HostStore !hsd -> case fromDynamic hsd of
              Just (d :: h) ->
                callFromEdhM (fn (NamedEdhArg d)) (ArgsPack args' kwargs')
              Nothing -> tryObjs rest
            _ -> tryObjs rest

-- receive named, optional arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (KnownSymbol name, EdhCallableM fn', Typeable h) =>
  EdhCallableM (NamedEdhArg (Maybe h) name -> fn')
  where
  callFromEdhM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !obj ->
          (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= goSearch args kwargs'
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
              <> " value for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] ->
          callFromEdhM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhObject !obj ->
            (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= goSearch args' kwargs'
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
                <> " value for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      goSearch :: [EdhValue] -> KwArgs -> [Object] -> Edh EdhValue
      goSearch args' kwargs' = tryObjs
        where
          tryObjs :: [Object] -> Edh EdhValue
          tryObjs [] =
            throwEdhM UsageError $ "arg host type mismatch: " <> argName
          tryObjs (obj : rest) = case edh'obj'store obj of
            HostStore !hsd -> case fromDynamic hsd of
              Just (d :: h) ->
                callFromEdhM
                  (fn (NamedEdhArg (Just d)))
                  (ArgsPack args' kwargs')
              Nothing -> tryObjs rest
            _ -> tryObjs rest

-- | Class for an object allocator implemented in the host language (which is
-- Haskell) that can be called from Edh code.
class EdhAllocatorM fn where
  allocObjM :: fn -> ArgsPack -> Edh (Maybe Unique, ObjectStore)

-- nullary base case
instance EdhAllocatorM (Edh (Maybe Unique, ObjectStore)) where
  allocObjM !fn apk@(ArgsPack !args !kwargs) =
    if null args && odNull kwargs
      then fn
      else
        edhValueReprM (EdhArgsPack apk) >>= \ !badRepr ->
          throwEdhM UsageError $ "extraneous arguments: " <> badRepr

-- repack rest-positional-args
instance EdhAllocatorM fn' => EdhAllocatorM ([EdhValue] -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    allocObjM (fn args) (ArgsPack [] kwargs)

instance EdhAllocatorM fn' => EdhAllocatorM (NamedEdhArg [EdhValue] name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    allocObjM (fn (NamedEdhArg args)) (ArgsPack [] kwargs)

-- repack rest-keyword-args
instance EdhAllocatorM fn' => EdhAllocatorM (KwArgs -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    allocObjM (fn kwargs) (ArgsPack args odEmpty)

instance EdhAllocatorM fn' => EdhAllocatorM (NamedEdhArg KwArgs name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    allocObjM (fn (NamedEdhArg kwargs)) (ArgsPack args odEmpty)

-- repack rest-pack-args
--
-- note it'll cause runtime error if @fn'@ takes further args
-- todo detect that case and report static errors?
instance EdhAllocatorM fn' => EdhAllocatorM (ArgsPack -> fn') where
  allocObjM !fn !apk = allocObjM (fn apk) (ArgsPack [] odEmpty)

instance EdhAllocatorM fn' => EdhAllocatorM (NamedEdhArg ArgsPack name -> fn') where
  allocObjM !fn !apk =
    allocObjM (fn (NamedEdhArg apk)) (ArgsPack [] odEmpty)

-- receive anonymous arg taking 'EdhValue'
instance EdhAllocatorM fn' => EdhAllocatorM (EdhValue -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) =
    allocObjM (fn val) (ArgsPack args kwargs)
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhValue'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe EdhValue -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) =
    allocObjM (fn (Just val)) (ArgsPack args kwargs)

-- receive anonymous arg taking a quantity value,
-- converted in to the designated uom
instance
  (EdhAllocatorM fn', KnownSymbol uom) =>
  EdhAllocatorM (QtyAsIn uom -> fn')
  where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhQty qty@(Quantity !q !u) ->
      if uomDefiIdent u == uomIdent
        then allocObjM (fn $ Qty q) (ArgsPack args kwargs)
        else mEdh $ \exit ->
          resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
            unifyToUnit
              uom
              (Right qty)
              ( \q' ets ->
                  runEdh
                    ets
                    (allocObjM (fn $ Qty q') (ArgsPack args kwargs))
                    exit
              )
              $ throwEdhTx UsageError $
                "arg uom mismatch: expect quantity in [" <> uomIdent
                  <> "] but given "
                  <> uomDefiIdent u
    EdhDecimal !d -> mEdh $ \exit ->
      resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
        unifyToUnit
          uom
          (Left d)
          ( \q' ets ->
              runEdh
                ets
                (allocObjM (fn $ Qty q') (ArgsPack args kwargs))
                exit
          )
          $ throwEdhTx UsageError $
            "arg uom mismatch: expect quantity in [" <> uomIdent
              <> "] but given a pure number"
    _ ->
      throwEdhM UsageError $
        "arg type mismatch: expect quantity in [" <> uomIdent
          <> "] but given "
          <> edhTypeNameOf val
    where
      !uomIdent = T.pack $ symbolVal (Proxy :: Proxy uom)
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking a quantity value,
-- converted in to the designated uom
instance
  (EdhAllocatorM fn', KnownSymbol uom) =>
  EdhAllocatorM (Maybe (QtyAsIn uom) -> fn')
  where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhQty qty@(Quantity !q !u) ->
      if uomDefiIdent u == uomIdent
        then allocObjM (fn $ Just $ Qty q) (ArgsPack args kwargs)
        else mEdh $ \exit ->
          resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
            unifyToUnit
              uom
              (Right qty)
              ( \q' ets ->
                  runEdh
                    ets
                    (allocObjM (fn $ Just $ Qty q') (ArgsPack args kwargs))
                    exit
              )
              $ throwEdhTx UsageError $
                "arg uom mismatch: expect quantity in [" <> uomIdent
                  <> "] but given "
                  <> uomDefiIdent u
    EdhDecimal !d -> mEdh $ \exit ->
      resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
        unifyToUnit
          uom
          (Left d)
          ( \q' ets ->
              runEdh
                ets
                (allocObjM (fn $ Just $ Qty q') (ArgsPack args kwargs))
                exit
          )
          $ throwEdhTx UsageError $
            "arg uom mismatch: expect quantity in [" <> uomIdent
              <> "] but given a pure number"
    _ ->
      throwEdhM UsageError $
        "arg type mismatch: expect quantity in [" <> uomIdent
          <> "] but given "
          <> edhTypeNameOf val
    where
      !uomIdent = T.pack $ symbolVal (Proxy :: Proxy uom)

-- receive anonymous arg taking 'Decimal'
instance EdhAllocatorM fn' => EdhAllocatorM (Decimal -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' -> allocObjM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Decimal'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Decimal -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' ->
      allocObjM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Double'
instance EdhAllocatorM fn' => EdhAllocatorM (Double -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in allocObjM (fn d) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Double'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Double -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in allocObjM (fn (Just d)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Float'
instance EdhAllocatorM fn' => EdhAllocatorM (Float -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in allocObjM (fn d) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Float'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Float -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' ->
      let !d = D.decimalToRealFloat val'
       in allocObjM (fn (Just d)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Integer'
instance EdhAllocatorM fn' => EdhAllocatorM (Integer -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> allocObjM (fn i) (ArgsPack args kwargs)
      _ -> throwEdhM UsageError "number type mismatch: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Integer'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Integer -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> allocObjM (fn (Just i)) (ArgsPack args kwargs)
      _ -> throwEdhM UsageError "number type mismatch: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Int'
instance EdhAllocatorM fn' => EdhAllocatorM (Int -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i -> allocObjM (fn $ fromInteger i) (ArgsPack args kwargs)
      _ -> throwEdhM UsageError "number type mismatch: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Int'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Int -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDecimal !val' -> case D.decimalToInteger val' of
      Just !i ->
        allocObjM (fn (Just $ fromInteger i)) (ArgsPack args kwargs)
      _ -> throwEdhM UsageError "number type mismatch: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Bool'
instance EdhAllocatorM fn' => EdhAllocatorM (Bool -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhBool !val' -> allocObjM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Bool'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Bool -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhBool !val' -> allocObjM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Blob'
instance EdhAllocatorM fn' => EdhAllocatorM (ByteString -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhBlob !val' -> allocObjM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Blob'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe ByteString -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhBlob !val' -> allocObjM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Text'
instance EdhAllocatorM fn' => EdhAllocatorM (Text -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhString !val' -> allocObjM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Text'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Text -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhString !val' -> allocObjM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Symbol'
instance EdhAllocatorM fn' => EdhAllocatorM (Symbol -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhSymbol !val' -> allocObjM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Symbol'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Symbol -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhSymbol !val' -> allocObjM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'UUID'
instance EdhAllocatorM fn' => EdhAllocatorM (UUID.UUID -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhUUID !val' -> allocObjM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'UUID'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe UUID.UUID -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhUUID !val' -> allocObjM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhPair'
instance EdhAllocatorM fn' => EdhAllocatorM ((EdhValue, EdhValue) -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhPair !v1 !v2 -> allocObjM (fn (v1, v2)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhPair'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe (EdhValue, EdhValue) -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhPair !v1 !v2 ->
      allocObjM (fn (Just (v1, v2))) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Dict'
instance EdhAllocatorM fn' => EdhAllocatorM (Dict -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDict !val' -> allocObjM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Dict'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Dict -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhDict !val' -> allocObjM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'List'
instance EdhAllocatorM fn' => EdhAllocatorM (List -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhList !val' -> allocObjM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'List'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe List -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhList !val' -> allocObjM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Object'
instance EdhAllocatorM fn' => EdhAllocatorM (Object -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhObject !val' -> allocObjM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Object'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Object -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhObject !val' -> allocObjM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhOrd'
instance EdhAllocatorM fn' => EdhAllocatorM (Ordering -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhOrd !val' -> allocObjM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhOrd'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Ordering -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhOrd !val' -> allocObjM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'Sink'
instance EdhAllocatorM fn' => EdhAllocatorM (Sink -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhSink !val' -> allocObjM (fn val') (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'Sink'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe Sink -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhSink !val' -> allocObjM (fn (Just val')) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'EdhNamedValue'
instance EdhAllocatorM fn' => EdhAllocatorM ((AttrName, EdhValue) -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhNamedValue !name !value ->
      allocObjM (fn (name, value)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'EdhNamedValue'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe (AttrName, EdhValue) -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhNamedValue !name !value ->
      allocObjM (fn (Just (name, value))) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'ExprDefi'
instance EdhAllocatorM fn' => EdhAllocatorM (ExprDefi -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhExpr !expr _src ->
      allocObjM (fn expr) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'ExprDefi'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe ExprDefi -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhExpr !expr _src ->
      allocObjM (fn (Just expr)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'ExprDefi' with src
instance EdhAllocatorM fn' => EdhAllocatorM ((ExprDefi, Text) -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhExpr !expr !src ->
      allocObjM (fn (expr, src)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'ExprDefi' with src
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe (ExprDefi, Text) -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhExpr !expr !src ->
      allocObjM (fn (Just (expr, src))) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'PositionalArgs'
instance EdhAllocatorM fn' => EdhAllocatorM (PositionalArgs -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if odNull kwargs''
        then allocObjM (fn (PositionalArgs args'')) (ArgsPack args kwargs)
        else throwEdhM UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'PositionalArgs'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe PositionalArgs -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if odNull kwargs''
        then
          allocObjM
            (fn (Just (PositionalArgs args'')))
            (ArgsPack args kwargs)
        else throwEdhM UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'KeywordArgs'
instance EdhAllocatorM fn' => EdhAllocatorM (KeywordArgs -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if null args''
        then allocObjM (fn (KeywordArgs kwargs'')) (ArgsPack args kwargs)
        else throwEdhM UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'KeywordArgs'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe KeywordArgs -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack (ArgsPack !args'' !kwargs'') ->
      if null args''
        then
          allocObjM
            (fn (Just (KeywordArgs kwargs'')))
            (ArgsPack args kwargs)
        else throwEdhM UsageError "extraneous kwargs for: anonymous"
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive anonymous arg taking 'PackedArgs'
instance EdhAllocatorM fn' => EdhAllocatorM (PackedArgs -> fn') where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack !apk ->
      allocObjM (fn (PackedArgs apk)) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking 'PackedArgs'
instance EdhAllocatorM fn' => EdhAllocatorM (Maybe PackedArgs -> fn') where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhArgsPack !apk ->
      allocObjM (fn (Just (PackedArgs apk))) (ArgsPack args kwargs)
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"

-- receive named arg taking 'EdhValue'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg EdhValue name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, kwargs') ->
        allocObjM (fn (NamedEdhArg val)) (ArgsPack args kwargs')
      (Nothing, kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        (val : args') ->
          allocObjM (fn (NamedEdhArg val)) (ArgsPack args' kwargs')
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhValue'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe EdhValue) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' ->
          allocObjM
            (fn (NamedEdhArg (Just val)))
            (ArgsPack args' kwargs')
      (!maybeVal, !kwargs') ->
        allocObjM (fn (NamedEdhArg maybeVal)) (ArgsPack args kwargs')
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking a quantity value,
-- converted in to the designated uom
instance
  (KnownSymbol name, KnownSymbol uom, EdhAllocatorM fn') =>
  EdhAllocatorM (NamedEdhArg (QtyAsIn uom) name -> fn')
  where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhQty qty@(Quantity !q !u) ->
          if uomDefiIdent u == uomIdent
            then
              allocObjM
                (fn (NamedEdhArg (Qty q)))
                (ArgsPack args kwargs')
            else mEdh $ \exit ->
              resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
                unifyToUnit
                  uom
                  (Right qty)
                  ( \q' ets ->
                      runEdh
                        ets
                        ( allocObjM
                            (fn (NamedEdhArg (Qty q')))
                            (ArgsPack args kwargs')
                        )
                        exit
                  )
                  $ throwEdhTx UsageError $
                    "arg uom mismatch: expect quantity in [" <> uomIdent
                      <> "] for "
                      <> argName
                      <> " but given "
                      <> uomDefiIdent u
        EdhDecimal !d -> mEdh $ \exit ->
          resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
            unifyToUnit
              uom
              (Left d)
              ( \q' ets ->
                  runEdh
                    ets
                    ( allocObjM
                        (fn (NamedEdhArg (Qty q')))
                        (ArgsPack args kwargs')
                    )
                    exit
              )
              $ throwEdhTx UsageError $
                "arg uom mismatch: expect quantity in [" <> uomIdent
                  <> "] for "
                  <> argName
                  <> " but given a pure number"
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect quantity in [" <> uomIdent <> "] for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhQty qty@(Quantity !q !u) ->
            if uomDefiIdent u == uomIdent
              then
                allocObjM
                  (fn (NamedEdhArg (Qty q)))
                  (ArgsPack args' kwargs')
              else mEdh $ \exit ->
                resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
                  unifyToUnit
                    uom
                    (Right qty)
                    ( \q' ets ->
                        runEdh
                          ets
                          ( allocObjM
                              (fn (NamedEdhArg (Qty q')))
                              (ArgsPack args' kwargs')
                          )
                          exit
                    )
                    $ throwEdhTx UsageError $
                      "arg uom mismatch: expect quantity in [" <> uomIdent
                        <> "] for "
                        <> argName
                        <> " but given "
                        <> uomDefiIdent u
          EdhDecimal !d -> mEdh $ \exit ->
            resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
              unifyToUnit
                uom
                (Left d)
                ( \q' ets ->
                    runEdh
                      ets
                      ( allocObjM
                          (fn (NamedEdhArg (Qty q')))
                          (ArgsPack args' kwargs')
                      )
                      exit
                )
                $ throwEdhTx UsageError $
                  "arg uom mismatch: expect quantity in [" <> uomIdent
                    <> "] for "
                    <> argName
                    <> " but given a pure number"
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect quantity in [" <> uomIdent <> "] for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      !uomIdent = T.pack $ symbolVal (Proxy :: Proxy uom)

-- receive named, optional arg taking a quantity value,
-- converted in to the designated uom
instance
  (KnownSymbol name, KnownSymbol uom, EdhAllocatorM fn') =>
  EdhAllocatorM (NamedEdhArg (Maybe (QtyAsIn uom)) name -> fn')
  where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhQty qty@(Quantity !q !u) ->
          if uomDefiIdent u == uomIdent
            then
              allocObjM
                (fn (NamedEdhArg $ Just $ Qty q))
                (ArgsPack args kwargs')
            else mEdh $ \exit ->
              resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
                unifyToUnit
                  uom
                  (Right qty)
                  ( \q' ets ->
                      runEdh
                        ets
                        ( allocObjM
                            (fn (NamedEdhArg $ Just $ Qty q'))
                            (ArgsPack args kwargs')
                        )
                        exit
                  )
                  $ throwEdhTx UsageError $
                    "arg uom mismatch: expect quantity in [" <> uomIdent
                      <> "] for "
                      <> argName
                      <> " but given "
                      <> uomDefiIdent u
        EdhDecimal !d -> mEdh $ \exit ->
          resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
            unifyToUnit
              uom
              (Left d)
              ( \q' ets ->
                  runEdh
                    ets
                    ( allocObjM
                        (fn (NamedEdhArg $ Just $ Qty q'))
                        (ArgsPack args kwargs')
                    )
                    exit
              )
              $ throwEdhTx UsageError $
                "arg uom mismatch: expect quantity in [" <> uomIdent
                  <> "] for "
                  <> argName
                  <> " but given a pure number"
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect quantity in [" <> uomIdent <> "] for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhQty qty@(Quantity !q !u) ->
            if uomDefiIdent u == uomIdent
              then
                allocObjM
                  (fn (NamedEdhArg $ Just $ Qty q))
                  (ArgsPack args' kwargs')
              else mEdh $ \exit ->
                resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
                  unifyToUnit
                    uom
                    (Right qty)
                    ( \q' ets ->
                        runEdh
                          ets
                          ( allocObjM
                              (fn (NamedEdhArg $ Just $ Qty q'))
                              (ArgsPack args' kwargs')
                          )
                          exit
                    )
                    $ throwEdhTx UsageError $
                      "arg uom mismatch: expect quantity in [" <> uomIdent
                        <> "] for "
                        <> argName
                        <> " but given "
                        <> uomDefiIdent u
          EdhDecimal !d -> mEdh $ \exit ->
            resolveUnitSpec (NamedUnit uomIdent) $ \uom ->
              unifyToUnit
                uom
                (Left d)
                ( \q' ets ->
                    runEdh
                      ets
                      ( allocObjM
                          (fn (NamedEdhArg $ Just $ Qty q'))
                          (ArgsPack args' kwargs')
                      )
                      exit
                )
                $ throwEdhTx UsageError $
                  "arg uom mismatch: expect quantity in [" <> uomIdent
                    <> "] for "
                    <> argName
                    <> " but given a pure number"
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect quantity in [" <> uomIdent <> "] for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
            where
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      !uomIdent = T.pack $ symbolVal (Proxy :: Proxy uom)

-- receive named arg taking 'Decimal'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Decimal name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          allocObjM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Decimal for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            allocObjM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Decimal for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Decimal'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Decimal) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          allocObjM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Decimal for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDecimal !val' ->
            allocObjM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Decimal for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Double'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Double name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in allocObjM (fn (NamedEdhArg d)) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Double for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in allocObjM (fn (NamedEdhArg d)) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Double for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Double'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Double) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in allocObjM
                (fn (NamedEdhArg (Just d)))
                (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Double for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in allocObjM
                  (fn (NamedEdhArg (Just d)))
                  (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Double for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Float'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Float name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in allocObjM (fn (NamedEdhArg d)) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Float for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in allocObjM (fn (NamedEdhArg d)) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Float for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Float'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Float) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' ->
          let !d = D.decimalToRealFloat val'
           in allocObjM
                (fn (NamedEdhArg (Just d)))
                (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Float for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDecimal !val' ->
            let !d = D.decimalToRealFloat val'
             in allocObjM
                  (fn (NamedEdhArg (Just d)))
                  (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Float for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Integer'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Integer name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            allocObjM (fn (NamedEdhArg i)) (ArgsPack args kwargs')
          _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Integer for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              allocObjM (fn (NamedEdhArg i)) (ArgsPack args' kwargs')
            _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Integer for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Integer'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Integer) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            allocObjM (fn (NamedEdhArg (Just i))) (ArgsPack args kwargs')
          _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Integer for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              allocObjM
                (fn (NamedEdhArg (Just i)))
                (ArgsPack args' kwargs')
            _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Integer for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Int'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Int name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            allocObjM
              (fn (NamedEdhArg $ fromInteger i))
              (ArgsPack args kwargs')
          _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Int for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              allocObjM
                (fn (NamedEdhArg $ fromInteger i))
                (ArgsPack args' kwargs')
            _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Int for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Int'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Int) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDecimal !val' -> case D.decimalToInteger val' of
          Just !i ->
            allocObjM
              (fn (NamedEdhArg (Just $ fromInteger i)))
              (ArgsPack args kwargs')
          _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Int for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDecimal !val' -> case D.decimalToInteger val' of
            Just !i ->
              allocObjM
                (fn (NamedEdhArg (Just $ fromInteger i)))
                (ArgsPack args' kwargs')
            _ -> throwEdhM UsageError $ "number type mismatch: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Int for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Bool'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Bool name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBool !val' ->
          allocObjM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Bool for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhBool !val' ->
            allocObjM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Bool for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Bool'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Bool) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBool !val' ->
          allocObjM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Bool for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhBool !val' ->
            allocObjM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Bool for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'ByteString'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg ByteString name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBlob !val' ->
          allocObjM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect ByteString for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhBlob !val' ->
            allocObjM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect ByteString for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'ByteString'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe ByteString) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhBlob !val' ->
          allocObjM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect ByteString for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhBlob !val' ->
            allocObjM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect ByteString for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Text'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Text name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhString !val' ->
          allocObjM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Text for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhString !val' ->
            allocObjM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Text for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Text'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Text) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhString !val' ->
          allocObjM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Text for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhString !val' ->
            allocObjM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Text for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Symbol'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Symbol name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSymbol !val' ->
          allocObjM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect symbol for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhSymbol !val' ->
            allocObjM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect symbol for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Symbol'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Symbol) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSymbol !val' ->
          allocObjM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect symbol for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhSymbol !val' ->
            allocObjM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect symbol for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'UUID'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg UUID.UUID name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhUUID !val' ->
          allocObjM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect UUID for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhUUID !val' ->
            allocObjM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect UUID for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'UUID'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe UUID.UUID) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhUUID !val' ->
          allocObjM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect UUID for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhUUID !val' ->
            allocObjM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect UUID for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhPair'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (EdhValue, EdhValue) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhPair !v1 !v2 ->
          allocObjM (fn (NamedEdhArg (v1, v2))) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect pair for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhPair !v1 !v2 ->
            allocObjM
              (fn (NamedEdhArg (v1, v2)))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect pair for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhPair'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe (EdhValue, EdhValue)) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhPair !v1 !v2 ->
          allocObjM
            (fn (NamedEdhArg (Just (v1, v2))))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect pair for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhPair !v1 !v2 ->
            allocObjM
              (fn (NamedEdhArg (Just (v1, v2))))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect pair for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Dict'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Dict name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDict !val' ->
          allocObjM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhDict !val' ->
            allocObjM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Dict'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Dict) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhDict !val' ->
          allocObjM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhDict !val' ->
            allocObjM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'List'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg List name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhList !val' ->
          allocObjM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect list for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhList !val' ->
            allocObjM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect list for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'List'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe List) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhList !val' ->
          allocObjM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect list for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhList !val' ->
            allocObjM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect list for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Object'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Object name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !val' ->
          allocObjM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect object for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhObject !val' ->
            allocObjM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect object for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Object'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Object) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !val' ->
          allocObjM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect object for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhObject !val' ->
            allocObjM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect object for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Ordering'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Ordering name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhOrd !val' ->
          allocObjM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Ordering for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhOrd !val' ->
            allocObjM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Ordering for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Ordering'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Ordering) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhOrd !val' ->
          allocObjM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Ordering for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhOrd !val' ->
            allocObjM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Ordering for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'Sink'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg Sink name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSink !val' ->
          allocObjM (fn (NamedEdhArg val')) (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect sink for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhSink !val' ->
            allocObjM (fn (NamedEdhArg val')) (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect sink for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'Sink'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe Sink) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhSink !val' ->
          allocObjM
            (fn (NamedEdhArg (Just val')))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect sink for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhSink !val' ->
            allocObjM
              (fn (NamedEdhArg (Just val')))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect sink for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'EdhNamedValue'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (AttrName, EdhValue) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhNamedValue !name !value ->
          allocObjM
            (fn (NamedEdhArg (name, value)))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhNamedValue !name !value ->
            allocObjM
              (fn (NamedEdhArg (name, value)))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'EdhNamedValue'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe (AttrName, EdhValue)) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhNamedValue !name !value ->
          allocObjM
            (fn (NamedEdhArg (Just (name, value))))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect term for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhNamedValue !name !value ->
            allocObjM
              (fn (NamedEdhArg (Just (name, value))))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect term for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'ExprDefi'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg ExprDefi name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr _src ->
          allocObjM
            (fn (NamedEdhArg expr))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhExpr !expr _src ->
            allocObjM
              (fn (NamedEdhArg expr))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'ExprDefi'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe ExprDefi) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr _src ->
          allocObjM
            (fn (NamedEdhArg (Just expr)))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhExpr !expr _src ->
            allocObjM
              (fn (NamedEdhArg (Just expr)))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'ExprDefi' with src
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (ExprDefi, Text) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr !src ->
          allocObjM
            (fn (NamedEdhArg (expr, src)))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhExpr !expr !src ->
            allocObjM
              (fn (NamedEdhArg (expr, src)))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'ExprDefi' with src
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe (ExprDefi, Text)) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhExpr !expr !src ->
          allocObjM
            (fn (NamedEdhArg (Just (expr, src))))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect Expr for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhExpr !expr !src ->
            allocObjM
              (fn (NamedEdhArg (Just (expr, src))))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect Expr for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'PositionalArgs'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg PositionalArgs name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if odNull kwargs''
            then
              allocObjM
                (fn (NamedEdhArg $ PositionalArgs args''))
                (ArgsPack args kwargs')
            else throwEdhM UsageError $ "extraneous kwargs for: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect tuple for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if odNull kwargs''
              then
                allocObjM
                  (fn (NamedEdhArg $ PositionalArgs args''))
                  (ArgsPack args' kwargs')
              else throwEdhM UsageError $ "extraneous kwargs for: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect tuple for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'PositionalArgs'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe PositionalArgs) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if odNull kwargs''
            then
              allocObjM
                (fn (NamedEdhArg $ Just $ PositionalArgs args''))
                (ArgsPack args kwargs')
            else throwEdhM UsageError $ "extraneous kwargs for: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect tuple for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if odNull kwargs''
              then
                allocObjM
                  (fn (NamedEdhArg $ Just $ PositionalArgs args''))
                  (ArgsPack args' kwargs')
              else throwEdhM UsageError $ "extraneous kwargs for: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect tuple for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'KeywordArgs'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg KeywordArgs name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if null args''
            then
              allocObjM
                (fn (NamedEdhArg $ KeywordArgs kwargs''))
                (ArgsPack args kwargs')
            else throwEdhM UsageError $ "extraneous pos args for: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect kwargs for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if null args''
              then
                allocObjM
                  (fn (NamedEdhArg $ KeywordArgs kwargs''))
                  (ArgsPack args' kwargs')
              else throwEdhM UsageError $ "extraneous pos args for: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect kwargs for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'KeywordArgs'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe KeywordArgs) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack (ArgsPack !args'' !kwargs'') ->
          if null args''
            then
              allocObjM
                (fn (NamedEdhArg $ Just $ KeywordArgs kwargs''))
                (ArgsPack args kwargs')
            else throwEdhM UsageError $ "extraneous pos args for: " <> argName
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect kwargs for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhArgsPack (ArgsPack !args'' !kwargs'') ->
            if null args''
              then
                allocObjM
                  (fn (NamedEdhArg $ Just $ KeywordArgs kwargs''))
                  (ArgsPack args' kwargs')
              else throwEdhM UsageError $ "extraneous pos args for: " <> argName
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect kwargs for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named arg taking 'PackedArgs'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg PackedArgs name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack !apk ->
          allocObjM
            (fn (NamedEdhArg $ PackedArgs apk))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect apk for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhArgsPack !apk ->
            allocObjM
              (fn (NamedEdhArg $ PackedArgs apk))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect apk for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- receive named, optional arg taking 'PackedArgs'
instance (KnownSymbol name, EdhAllocatorM fn') => EdhAllocatorM (NamedEdhArg (Maybe PackedArgs) name -> fn') where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhArgsPack !apk ->
          allocObjM
            (fn (NamedEdhArg (Just $ PackedArgs apk)))
            (ArgsPack args kwargs')
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect apk for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhArgsPack !apk ->
            allocObjM
              (fn (NamedEdhArg (Just $ PackedArgs apk)))
              (ArgsPack args' kwargs')
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect apk for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)

-- * general instances

{- HLINT ignore "Redundant <$>" -}

-- receive anonymous arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (EdhAllocatorM fn', Typeable h) =>
  EdhAllocatorM (h -> fn')
  where
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhObject !obj -> (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= tryObjs
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
    where
      tryObjs :: [Object] -> Edh (Maybe Unique, ObjectStore)
      tryObjs [] = throwEdhM UsageError "arg host type mismatch: anonymous"
      tryObjs (obj : rest) = case edh'obj'store obj of
        HostStore !hsd -> case fromDynamic hsd of
          Just (d :: h) ->
            allocObjM (fn d) (ArgsPack args kwargs)
          Nothing -> tryObjs rest
        _ -> tryObjs rest
  allocObjM _ _ = throwEdhM UsageError "missing anonymous arg"

-- receive optional anonymous arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (EdhAllocatorM fn', Typeable h) =>
  EdhAllocatorM (Maybe h -> fn')
  where
  allocObjM !fn (ArgsPack [] !kwargs) =
    allocObjM (fn Nothing) (ArgsPack [] kwargs)
  allocObjM !fn (ArgsPack (val : args) !kwargs) = case val of
    EdhObject !obj -> (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= tryObjs
    _ -> throwEdhM UsageError "arg type mismatch: anonymous"
    where
      tryObjs :: [Object] -> Edh (Maybe Unique, ObjectStore)
      tryObjs [] = throwEdhM UsageError "arg host type mismatch: anonymous"
      tryObjs (obj : rest) = case edh'obj'store obj of
        HostStore !hsd -> case fromDynamic hsd of
          Just (d :: h) ->
            allocObjM (fn (Just d)) (ArgsPack args kwargs)
          Nothing -> tryObjs rest
        _ -> tryObjs rest

-- receive named arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (KnownSymbol name, EdhAllocatorM fn', Typeable h) =>
  EdhAllocatorM (NamedEdhArg h name -> fn')
  where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !obj ->
          (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= goSearch args kwargs'
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
              <> " value for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] -> throwEdhM UsageError $ "missing named arg: " <> argName
        val : args' -> case val of
          EdhObject !obj ->
            (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= goSearch args' kwargs'
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
                <> " value for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      goSearch :: [EdhValue] -> KwArgs -> [Object] -> Edh (Maybe Unique, ObjectStore)
      goSearch args' kwargs' = tryObjs
        where
          tryObjs :: [Object] -> Edh (Maybe Unique, ObjectStore)
          tryObjs [] =
            throwEdhM UsageError $ "arg host type mismatch: " <> argName
          tryObjs (obj : rest) = case edh'obj'store obj of
            HostStore !hsd -> case fromDynamic hsd of
              Just (d :: h) ->
                allocObjM (fn (NamedEdhArg d)) (ArgsPack args' kwargs')
              Nothing -> tryObjs rest
            _ -> tryObjs rest

-- receive named, optional arg taking specific host storage
instance
  {-# OVERLAPPABLE #-}
  (KnownSymbol name, EdhAllocatorM fn', Typeable h) =>
  EdhAllocatorM (NamedEdhArg (Maybe h) name -> fn')
  where
  allocObjM !fn (ArgsPack !args !kwargs) =
    case odTakeOut (AttrByName argName) kwargs of
      (Just !val, !kwargs') -> case val of
        EdhObject !obj ->
          (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= goSearch args kwargs'
        _ ->
          throwEdhM UsageError $
            "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
              <> " value for "
              <> argName
              <> " but given "
              <> edhTypeNameOf val
      (Nothing, !kwargs') -> case args of
        [] ->
          allocObjM (fn (NamedEdhArg Nothing)) (ArgsPack [] kwargs')
        val : args' -> case val of
          EdhObject !obj ->
            (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= goSearch args' kwargs'
          _ ->
            throwEdhM UsageError $
              "arg type mismatch: expect host " <> T.pack (show $ typeRep @h)
                <> " value for "
                <> argName
                <> " but given "
                <> edhTypeNameOf val
    where
      !argName = T.pack $ symbolVal (Proxy :: Proxy name)
      goSearch :: [EdhValue] -> KwArgs -> [Object] -> Edh (Maybe Unique, ObjectStore)
      goSearch args' kwargs' = tryObjs
        where
          tryObjs :: [Object] -> Edh (Maybe Unique, ObjectStore)
          tryObjs [] =
            throwEdhM UsageError $ "arg host type mismatch: " <> argName
          tryObjs (obj : rest) = case edh'obj'store obj of
            HostStore !hsd -> case fromDynamic hsd of
              Just (d :: h) ->
                allocObjM
                  (fn (NamedEdhArg (Just d)))
                  (ArgsPack args' kwargs')
              Nothing -> tryObjs rest
            _ -> tryObjs rest
