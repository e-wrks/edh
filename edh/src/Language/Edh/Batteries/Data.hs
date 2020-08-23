
module Language.Edh.Batteries.Data where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad.Reader
import           Control.Concurrent.STM

import           Data.Unique
import qualified Data.Text                     as T
import qualified Data.Text.Encoding            as TE
import qualified Data.HashMap.Strict           as Map

import qualified Data.UUID                     as UUID

import           Data.Lossless.Decimal         as D

import           Language.Edh.Control
import           Language.Edh.Event
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate
import           Language.Edh.Details.Utils


strEncodeProc :: EdhHostProc
strEncodeProc (ArgsPack [EdhString !str] !kwargs) !exit | odNull kwargs =
  exitEdhTx exit $ EdhBlob $ TE.encodeUtf8 str
strEncodeProc _ _ =
  throwEdhTx EvalError "bug: __StringType_bytes__ got unexpected args"

blobDecodeProc :: EdhHostProc
blobDecodeProc (ArgsPack [EdhBlob !blob] !kwargs) !exit | odNull kwargs =
  exitEdhTx exit $ EdhString $ TE.decodeUtf8 blob
blobDecodeProc _ _ =
  throwEdhTx EvalError "bug: __BlobType_utf8string__ got unexpected args"


propertyProc :: EdhHostProc
propertyProc !apk !exit !ets = case edh'obj'store caller'this of
  ClassStore (Class _ !cs _) -> defProp cs
  HashStore !hs -> defProp hs
  _ -> throwEdh ets UsageError "can not define property for a host object"
 where
  !ctx         = edh'context ets
  !caller'this = edh'scope'this $ contextFrame ctx 1

  defProp :: EntityStore -> STM ()
  defProp !es = case parseArgsPack (Nothing, Nothing) argsParser apk of
    Left !err -> throwEdh ets UsageError err
    Right (Nothing, _) ->
      throwEdh ets UsageError "missing getter method to define a property"
    Right (Just getter, setter) -> do
      let !pd   = EdhProcedure (EdhDescriptor getter setter) Nothing
          !name = edh'procedure'name getter
      when (name /= AttrByName "_") $ unless (edh'ctx'pure ctx) $ iopdInsert
        name
        pd
        es
      exitEdhSTM ets exit pd

  argsParser =
    ArgsPackParser
        [ \arg (_, setter) -> case arg of
          EdhProcedure (EdhMethod !getter) _     -> Right (Just getter, setter)
          -- todo is this right? to unbind a bound method to define a new prop
          EdhBoundProc (EdhMethod !getter) _ _ _ -> Right (Just getter, setter)
          !badVal ->
            Left
              $  "need a method procedure to define a property, not a: "
              <> T.pack (edhTypeNameOf badVal)
        , \arg (getter, _) -> case arg of
          EdhProcedure (EdhMethod !setter) _     -> Right (getter, Just setter)
          -- todo is this right? to unbind a bound method to define a new prop
          EdhBoundProc (EdhMethod !setter) _ _ _ -> Right (getter, Just setter)
          !badVal ->
            Left
              $  "need a method procedure to define a property, not a: "
              <> T.pack (edhTypeNameOf badVal)
        ]
      $ Map.fromList
          [ ( "getter"
            , \arg (_, setter) -> case arg of
              EdhProcedure (EdhMethod !getter) _ -> Right (Just getter, setter)
          -- todo is this right? to unbind a bound method to define a new prop
              EdhBoundProc (EdhMethod !getter) _ _ _ ->
                Right (Just getter, setter)
              !badVal ->
                Left
                  $  "need a method procedure to define a property, not a: "
                  <> T.pack (edhTypeNameOf badVal)
            )
          , ( "setter"
            , \arg (getter, _) -> case arg of
              EdhProcedure (EdhMethod !setter) _ -> Right (getter, Just setter)
          -- todo is this right? to unbind a bound method to define a new prop
              EdhBoundProc (EdhMethod !setter) _ _ _ ->
                Right (getter, Just setter)
              !badVal ->
                Left
                  $  "need a method procedure to define a property, not a: "
                  <> T.pack (edhTypeNameOf badVal)
            )
          ]

setterProc :: EdhHostProc
setterProc (ArgsPack !args !kwargs) !exit !ets =
  case edh'obj'store caller'this of
    ClassStore (Class _ !cs _) -> defProp cs
    HashStore !hs -> defProp hs
    _ -> throwEdh ets UsageError "can not define property for a host object"
 where
  !ctx         = edh'context ets
  !caller'this = edh'scope'this $ contextFrame ctx 1

  defProp :: EntityStore -> STM ()
  defProp !es = case args of
    [EdhProcedure (EdhMethod !setter) _] | odNull kwargs -> findGetter es setter
    [EdhBoundProc (EdhMethod !setter) _ _ _] | odNull kwargs ->
      findGetter es setter
    _ -> throwEdh ets EvalError "invalid args to setter"

  findGetter :: EntityStore -> ProcDefi -> STM ()
  findGetter !es !setter = iopdLookup name es >>= \case
    Just (EdhProcedure (EdhDescriptor !getter _) _) ->
      setSetter es setter getter
    Just (EdhBoundProc (EdhDescriptor !getter _) _ _ _) ->
      setSetter es setter getter
    _ ->
      throwEdh ets UsageError $ "missing property getter " <> T.pack (show name)
    where !name = edh'procedure'name setter

  setSetter :: EntityStore -> ProcDefi -> ProcDefi -> STM ()
  setSetter !es !setter !getter = do
    let !pd = EdhProcedure (EdhDescriptor getter $ Just setter) Nothing
    unless (edh'ctx'pure ctx) $ iopdInsert name pd es
    exitEdhSTM ets exit pd
    where !name = edh'procedure'name setter


-- | operator (@) - attribute key dereferencing
attrDerefAddrProc :: EdhIntrinsicOp
attrDerefAddrProc !lhExpr !rhExpr !exit = evalExpr rhExpr $ \ !rhVal ->
  case edhUltimate rhVal of
    EdhExpr _ (AttrExpr (DirectRef !addr)) _ -> \ !ets ->
      resolveEdhAttrAddr ets addr $ \ !key ->
        runEdhTx ets $ getEdhAttr lhExpr key (noAttr $ attrKeyStr key) exit
    EdhString !attrName ->
      getEdhAttr lhExpr (AttrByName attrName) (noAttr attrName) exit
    EdhSymbol sym@(Symbol _ !symRepr) ->
      getEdhAttr lhExpr (AttrBySym sym) (noAttr symRepr) exit
    _ -> throwEdhTx EvalError $ "invalid attribute reference type - " <> T.pack
      (edhTypeNameOf rhVal)
 where
  noAttr !keyRepr !lhVal =
    throwEdhTx EvalError
      $  "no such attribute "
      <> keyRepr
      <> " from a "
      <> T.pack (edhTypeNameOf lhVal)
      <> ": "
      <> T.pack (show lhVal)

-- | operator (?@) - attribute dereferencing tempter, 
-- address an attribute off an object if possible, nil otherwise
attrDerefTemptProc :: EdhIntrinsicOp
attrDerefTemptProc !lhExpr !rhExpr !exit = evalExpr rhExpr $ \ !rhVal ->
  case edhUltimate rhVal of
    EdhExpr _ (AttrExpr (DirectRef !addr)) _ -> \ !ets ->
      resolveEdhAttrAddr ets addr
        $ \ !key -> runEdhTx ets $ getEdhAttr lhExpr key noAttr exit
    EdhString !attrName -> getEdhAttr lhExpr (AttrByName attrName) noAttr exit
    EdhSymbol !sym      -> getEdhAttr lhExpr (AttrBySym sym) noAttr exit
    _ ->
      throwEdhTx EvalError $ "invalid attribute reference type - " <> T.pack
        (edhTypeNameOf rhVal)
  where noAttr _ = exitEdhTx exit nil

-- | operator (?) - attribute tempter, 
-- address an attribute off an object if possible, nil otherwise
attrTemptProc :: EdhIntrinsicOp
attrTemptProc !lhExpr !rhExpr !exit !ets = case rhExpr of
  AttrExpr (DirectRef !addr) -> resolveEdhAttrAddr ets addr $ \ !key ->
    runEdhTx ets $ getEdhAttr lhExpr key (const $ exitEdhTx exit nil) exit
  _ -> throwEdh ets EvalError $ "invalid attribute expression: " <> T.pack
    (show rhExpr)


-- | operator ($) - function application
--
-- similar to ($) operator in Haskell
-- can be used to apply decorators with nicer syntax
fapProc :: EdhIntrinsicOp
fapProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    -- special case, support merging of apks with func app syntax, so args can
    -- be chained then applied to some function
    EdhArgsPack (ArgsPack !args !kwargs) -> evalExpr rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhArgsPack (ArgsPack !args' !kwargs') -> \ !ets -> do
          !kwIOPD <- iopdFromList $ odToList kwargs
          iopdUpdate (odToList kwargs') kwIOPD
          !kwargs'' <- iopdSnapshot kwIOPD
          exitEdhSTM ets exit $ EdhArgsPack $ ArgsPack (args ++ args') kwargs''
        _ -> exitEdhTx exit $ EdhArgsPack $ ArgsPack (args ++ [rhVal]) kwargs
    -- normal case
    !calleeVal -> \ !ets -> packEdhArgs ets argsPkr $ \ !apk ->
      edhPrepareCall' ets calleeVal (deApk apk)
        $ \ !mkCall -> runEdhTx ets (mkCall exit)
 where
  argsPkr :: ArgsPacker
  argsPkr = case rhExpr of
    ArgsPackExpr !pkr -> pkr
    _                 -> [SendPosArg rhExpr]

-- | operator (|) - flipped function application
--
-- similar to UNIX pipe
ffapProc :: EdhIntrinsicOp
ffapProc !lhExpr !rhExpr = fapProc rhExpr lhExpr


-- | operator (:=) - named value definition
defProc :: EdhIntrinsicOp
defProc (AttrExpr (DirectRef (NamedAttr !valName))) !rhExpr !exit = do
  ets <- ask
  evalExpr rhExpr $ \ !rhV -> do
    let !rhVal   = edhDeCaseClose rhV
        !ctx     = edh'context ets
        !scope   = contextScope ctx
        this     = edh'scope'this scope
        !nv      = EdhNamedValue valName rhVal
        doAssign = do
          changeEntityAttr ets (scopeEntity scope) (AttrByName valName) nv
          when (contextExporting ctx && objEntity this == scopeEntity scope)
            $   lookupEntityAttr ets
                                 (objEntity this)
                                 (AttrByName edhExportsMagicName)
            >>= \case
                  EdhDict (Dict _ !thisExpDS) ->
                    iopdInsert (EdhString valName) nv thisExpDS
                  _ -> do
                    d <- EdhDict <$> createEdhDict [(EdhString valName, nv)]
                    changeEntityAttr ets
                                     (objEntity this)
                                     (AttrByName edhExportsMagicName)
                                     d
    lookupEntityAttr ets (scopeEntity scope) (AttrByName valName) >>= \case
      EdhNil -> do
        doAssign
        exitEdhSTM ets exit nv
      oldDef@(EdhNamedValue n v) -> if v /= rhVal
        then runEdhTx ets $ edhValueRepr rhVal $ \ !newR ->
          edhValueRepr oldDef $ \ !oldR -> case newR of
            EdhString !newRepr -> case oldR of
              EdhString oldRepr ->
                throwEdhTx EvalError
                  $  "can not redefine "
                  <> valName
                  <> " from { "
                  <> oldRepr
                  <> " } to { "
                  <> newRepr
                  <> " }"
              _ -> error "bug: edhValueRepr returned non-string"
            _ -> error "bug: edhValueRepr returned non-string"
        else do
          -- avoid writing the entity if all same
          unless (n == valName) doAssign
          exitEdhSTM ets exit nv
      _ -> do
        doAssign
        exitEdhSTM ets exit nv
defProc !lhExpr _ _ =
  throwEdhTx EvalError $ "invalid value definition: " <> T.pack (show lhExpr)


-- | operator (?:=) - named value definition if missing
defMissingProc :: EdhIntrinsicOp
defMissingProc (AttrExpr (DirectRef (NamedAttr "_"))) _ _ =
  throwEdhTx UsageError "not so reasonable: _ ?:= xxx"
defMissingProc (AttrExpr (DirectRef (NamedAttr !valName))) !rhExpr !exit = do
  ets <- ask
  let !ent   = scopeEntity $ contextScope $ edh'context ets
      !key   = AttrByName valName
      !etsTx = ets { edh'in'tx = True } -- must within a tx
  lookupEntityAttr etsTx ent key >>= \case
    EdhNil -> runEdhTx etsTx $ evalExpr rhExpr $ \ !rhV -> do
      let !rhVal = edhDeCaseClose rhV
          !nv    = EdhNamedValue valName rhVal
      changeEntityAttr etsTx ent key nv
      exitEdhSTM ets exit nv
    !preVal -> exitEdhSTM ets exit preVal
defMissingProc !lhExpr _ _ =
  throwEdhTx EvalError $ "invalid value definition: " <> T.pack (show lhExpr)


-- | operator (:) - pair constructor
pairCtorProc :: EdhIntrinsicOp
pairCtorProc !lhExpr !rhExpr !exit = do
  ets <- ask
  -- make sure left hand and right hand values are evaluated in same tx
  local (const ets { edh'in'tx = True })
    $ evalExpr lhExpr
    $ \ !lhVal -> evalExpr rhExpr $ \ !rhVal -> exitEdhSTM
        ets
        exit
        (EdhPair (edhDeCaseClose lhVal) (edhDeCaseClose rhVal))


-- | the Symbol(repr, *reprs) constructor
symbolCtorProc :: EdhHostProc
symbolCtorProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
  throwEdhTx UsageError "no kwargs should be passed to Symbol()"
symbolCtorProc (ArgsPack !reprs _) !exit = ask >>= \ets -> do
  let ctorSym :: EdhValue -> (Symbol -> STM ()) -> STM ()
      ctorSym (EdhString !repr) !exit' = mkSymbol repr >>= exit'
      ctorSym _ _ = throwEdh ets EvalError "invalid arg to Symbol()"
  seqcontSTM (ctorSym <$> reprs) $ \case
    [sym] -> exitEdhSTM ets exit $ EdhSymbol sym
    syms ->
      exitEdhSTM ets exit $ EdhArgsPack $ ArgsPack (EdhSymbol <$> syms) odEmpty


uuidCtorProc :: EdhHostProc
uuidCtorProc (ArgsPack [] !kwargs) !exit | odNull kwargs =
  ask >>= \ !ets -> EdhUUID <$> mkUUID >>= exitEdhSTM ets exit
uuidCtorProc (ArgsPack [EdhString !uuidTxt] !kwargs) !exit | odNull kwargs =
  case UUID.fromText uuidTxt of
    Just !uuid -> exitEdhTx exit $ EdhUUID uuid
    _          -> throwEdhTx UsageError $ "invalid uuid string: " <> uuidTxt
-- todo support more forms of UUID ctor args
uuidCtorProc _ _ = throwEdhTx UsageError "invalid args to UUID()"


apkArgsProc :: EdhHostProc
apkArgsProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
  throwEdhTx EvalError "bug: __ArgsPackType_args__ got kwargs"
apkArgsProc (ArgsPack [EdhArgsPack (ArgsPack !args _)] _) !exit =
  exitEdhTx exit $ EdhArgsPack $ ArgsPack args odEmpty
apkArgsProc _ _ =
  throwEdhTx EvalError "bug: __ArgsPackType_args__ got unexpected args"

apkKwrgsProc :: EdhHostProc
apkKwrgsProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
  throwEdhTx EvalError "bug: __ArgsPackType_kwargs__ got kwargs"
apkKwrgsProc (ArgsPack [EdhArgsPack (ArgsPack _ !kwargs')] _) !exit =
  exitEdhTx exit $ EdhArgsPack $ ArgsPack [] kwargs'
apkKwrgsProc _ _ =
  throwEdhTx EvalError "bug: __ArgsPackType_kwargs__ got unexpected args"


-- | utility repr(*args,**kwargs) - repr extractor
reprProc :: EdhHostProc
reprProc (ArgsPack !args !kwargs) !exit = do
  ets <- ask
  let
    go
      :: [EdhValue]
      -> [(AttrKey, EdhValue)]
      -> [EdhValue]
      -> [(AttrKey, EdhValue)]
      -> STM ()
    go [repr] kwReprs [] [] | null kwReprs = exitEdhSTM ets exit repr
    go reprs kwReprs [] [] =
      exitEdhSTM ets exit $ EdhArgsPack $ ArgsPack (reverse reprs) $ odFromList
        kwReprs
    go reprs kwReprs (v : rest) kwps =
      runEdhTx ets $ edhValueRepr v $ \ !r -> go (r : reprs) kwReprs rest kwps
    go reprs kwReprs [] ((k, v) : rest) =
      runEdhTx ets $ edhValueRepr v $ \ !r ->
        go reprs ((k, r) : kwReprs) [] rest
  go [] [] args (odToList kwargs)


capProc :: EdhHostProc
capProc (ArgsPack [!v] !kwargs) !exit = do
  !ets <- ask
  case edhUltimate v of
    EdhObject !o -> lookupEdhObjAttr ets o (AttrByName "__cap__") >>= \case
      EdhNil -> exitEdhSTM ets exit $ EdhDecimal D.nan
      EdhMethod !mth ->
        runEdhTx ets $ callEdhMethod o mth (ArgsPack [] kwargs) id exit
      !badMagic ->
        throwEdh ets UsageError
          $  "bad magic __cap__ of "
          <> T.pack (edhTypeNameOf badMagic)
          <> " on class "
          <> procedureName (objClass o)
    _ -> exitEdhSTM ets exit $ EdhDecimal D.nan
capProc _ _ =
  throwEdhTx UsageError "please get capacity of one value at a time"

growProc :: EdhHostProc
growProc (ArgsPack [!v, newCap@EdhDecimal{}] !kwargs) !exit = do
  !ets <- ask
  case edhUltimate v of
    EdhObject !o -> lookupEdhObjAttr ets o (AttrByName "__grow__") >>= \case
      EdhNil ->
        throwEdh ets UsageError
          $  "grow() not supported by the object of class "
          <> procedureName (objClass o)
      EdhMethod !mth ->
        runEdhTx ets $ callEdhMethod o mth (ArgsPack [newCap] kwargs) id exit
      !badMagic ->
        throwEdh ets UsageError
          $  "bad magic __grow__ of "
          <> T.pack (edhTypeNameOf badMagic)
          <> " on class "
          <> procedureName (objClass o)
    !badVal ->
      throwEdh ets UsageError $ "grow() not supported by a value of " <> T.pack
        (edhTypeNameOf badVal)
growProc _ _ =
  throwEdhTx UsageError "invalid args to grow(container, newCapacity)"

lenProc :: EdhHostProc
lenProc (ArgsPack [!v] !kwargs) !exit = do
  !ets <- ask
  case edhUltimate v of
    EdhObject !o -> lookupEdhObjAttr ets o (AttrByName "__len__") >>= \case
      EdhNil -> exitEdhSTM ets exit $ EdhDecimal D.nan
      EdhMethod !mth ->
        runEdhTx ets $ callEdhMethod o mth (ArgsPack [] kwargs) id exit
      !badMagic ->
        throwEdh ets UsageError
          $  "bad magic __len__ of "
          <> T.pack (edhTypeNameOf badMagic)
          <> " on class "
          <> procedureName (objClass o)
    EdhList (List _ !lv) -> length <$> readTVar lv >>= \ !llen ->
      exitEdhSTM ets exit $ EdhDecimal $ fromIntegral llen
    EdhDict (Dict _ !ds) -> iopdSize ds
      >>= \ !dlen -> exitEdhSTM ets exit $ EdhDecimal $ fromIntegral dlen
    EdhArgsPack (ArgsPack !posArgs !kwArgs) | odNull kwArgs ->
      -- no keyword arg, assuming tuple semantics
      exitEdhSTM ets exit $ EdhDecimal $ fromIntegral $ length posArgs
    EdhArgsPack (ArgsPack !posArgs !kwArgs) | null posArgs ->
      -- no positional arg, assuming named tuple semantics
      exitEdhSTM ets exit $ EdhDecimal $ fromIntegral $ odSize kwArgs
    EdhArgsPack{} -> throwEdh
      ets
      UsageError
      "unresonable to get length of an apk with both positional and keyword args"
    _ -> exitEdhSTM ets exit $ EdhDecimal D.nan
lenProc _ _ = throwEdhTx UsageError "please get length of one value at a time"

markProc :: EdhHostProc
markProc (ArgsPack [!v, newLen@EdhDecimal{}] !kwargs) !exit = do
  !ets <- ask
  case edhUltimate v of
    EdhObject !o -> lookupEdhObjAttr ets o (AttrByName "__mark__") >>= \case
      EdhNil ->
        throwEdh ets UsageError
          $  "mark() not supported by the object of class "
          <> procedureName (objClass o)
      EdhMethod !mth ->
        runEdhTx ets $ callEdhMethod o mth (ArgsPack [newLen] kwargs) id exit
      !badMagic ->
        throwEdh ets UsageError
          $  "bad magic __mark__ of "
          <> T.pack (edhTypeNameOf badMagic)
          <> " on class "
          <> procedureName (objClass o)
    !badVal ->
      throwEdh ets UsageError $ "mark() not supported by a value of " <> T.pack
        (edhTypeNameOf badVal)
markProc _ _ =
  throwEdhTx UsageError "invalid args to mark(container, newLength)"


showProc :: EdhHostProc
showProc (ArgsPack [!v] !kwargs) !exit = do
  !ets <- ask
  let -- todo specialize more informative show for intrinsic types of values
    showWithNoMagic = edhValueReprSTM ets v $ \ !r ->
      exitEdhSTM ets exit $ EdhString $ T.pack (edhTypeNameOf v) <> ": " <> r
  case edhUltimate v of
    EdhObject !o -> lookupEdhObjAttr ets o (AttrByName "__show__") >>= \case
      EdhNil -> showWithNoMagic
      EdhMethod !mth ->
        runEdhTx ets $ callEdhMethod o mth (ArgsPack [] kwargs) id exit
      !badMagic ->
        throwEdh ets UsageError
          $  "bad magic __show__ of "
          <> T.pack (edhTypeNameOf badMagic)
          <> " on class "
          <> procedureName (objClass o)
    _ -> showWithNoMagic
showProc _ _ = throwEdhTx UsageError "please show one value at a time"

descProc :: EdhHostProc
descProc (ArgsPack [!v] !kwargs) !exit = do
  !ets <- ask
  let -- TODO specialize more informative description (statistical wise) for
      --      intrinsic types of values
      descWithNoMagic = edhValueReprSTM ets v $ \ !r -> case v of
        EdhObject !o ->
          exitEdhSTM ets exit
            $  EdhString
            $  "it is an object of class "
            <> procedureName (objClass o)
            <> ", having representation:\n"
            <> r
        _ ->
          exitEdhSTM ets exit
            $  EdhString
            $  "it is of "
            <> T.pack (edhTypeNameOf v)
            <> ", having representation:\n"
            <> r
  case edhUltimate v of
    EdhObject !o -> lookupEdhObjAttr ets o (AttrByName "__desc__") >>= \case
      EdhNil -> descWithNoMagic
      EdhMethod !mth ->
        runEdhTx ets $ callEdhMethod o mth (ArgsPack [] kwargs) id exit
      !badMagic ->
        throwEdh ets UsageError
          $  "bad magic __desc__ of "
          <> T.pack (edhTypeNameOf badMagic)
          <> " on class "
          <> procedureName (objClass o)
    _ -> descWithNoMagic
descProc _ _ = throwEdhTx UsageError "please describe one value at a time"


-- | operator (++) - string coercing concatenator
concatProc :: EdhIntrinsicOp
concatProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhv ->
  case edhUltimate lhv of
    EdhBlob !lhBlob -> evalExpr rhExpr $ \ !rhv -> case edhUltimate rhv of
      EdhBlob !rhBlob -> exitEdhTx exit $ EdhBlob $ lhBlob <> rhBlob
      EdhString !rhStr ->
        exitEdhTx exit $ EdhBlob $ lhBlob <> TE.encodeUtf8 rhStr
      rhVal ->
        throwEdhTx UsageError
          $  "should not (++) a "
          <> T.pack (edhTypeNameOf rhVal)
          <> " to a blob."
    lhVal -> edhValueStr lhVal $ \lhStr -> case lhStr of
      EdhString !lhs -> evalExpr rhExpr $ \ !rhv ->
        edhValueStr (edhDeCaseClose $ edhUltimate rhv) $ \ !rhStr ->
          case rhStr of
            EdhString !rhs -> exitEdhTx exit (EdhString $ lhs <> rhs)
            _              -> error "bug: edhValueStr returned non-string"
      _ -> error "bug: edhValueStr returned non-string"


-- | utility null(*args,**kwargs) - null tester
isNullProc :: EdhHostProc
isNullProc (ArgsPack !args !kwargs) !exit = do
  !ets <- ask
  if odNull kwargs
    then case args of
      [v] ->
        edhValueNull ets v $ \isNull -> exitEdhSTM ets exit $ EdhBool isNull
      _ -> seqcontSTM (edhValueNull ets <$> args) $ \ !argsNulls ->
        exitEdhSTM ets exit $ EdhArgsPack $ ArgsPack (EdhBool <$> argsNulls)
                                                     odEmpty
    else seqcontSTM (edhValueNull ets <$> args) $ \argsNulls ->
      seqcontSTM
          [ \exit' ->
              edhValueNull ets v (\ !isNull -> exit' (k, EdhBool isNull))
          | (k, v) <- odToList kwargs
          ]
        $ \ !kwargsNulls -> exitEdhSTM
            ets
            exit
            ( EdhArgsPack
            $ ArgsPack (EdhBool <$> argsNulls) (odFromList kwargsNulls)
            )


-- | utility type(*args,**kwargs) - value type introspector
typeProc :: EdhHostProc
typeProc (ArgsPack !args !kwargs) !exit =
  let !argsType = edhTypeValOf <$> args
  in  if odNull kwargs
        then case argsType of
          [t] -> exitEdhTx exit t
          _   -> exitEdhTx exit $ EdhArgsPack $ ArgsPack argsType odEmpty
        else exitEdhTx
          exit
          (EdhArgsPack $ ArgsPack argsType $ odMap edhTypeValOf kwargs)
 where
  edhTypeValOf :: EdhValue -> EdhValue
  edhTypeValOf EdhNil              = EdhNil
  edhTypeValOf (EdhNamedValue n v) = EdhNamedValue n $ edhTypeValOf v
  edhTypeValOf v                   = EdhType $ edhTypeOf v


procNameProc :: EdhHostProc
procNameProc (ArgsPack !args !kwargs) !exit !ets = case args of
  [!p] | odNull kwargs -> case p of
    EdhProcedure !callable _             -> cpName callable
    EdhBoundProc !callable _this _that _ -> cpName callable
  _ -> throwEdh ets EvalError "bug: __ProcType_name__ got unexpected args"
 where
  cpName :: EdhCallable -> STM ()
  cpName = \case
    EdhIntrOp _ (IntrinOpDefi _ !opSym _) ->
      exitEdhTx exit $ EdhString $ "(" <> opSym <> ")"
    EdhMethod !pd     -> exitEdhTx exit $ EdhString $ procedureName pd
    EdhOprtor _ _ !pd -> exitEdhTx exit $ EdhString $ procedureName pd
    EdhGnrtor !pd     -> exitEdhTx exit $ EdhString $ procedureName pd
    EdhIntrpr !pd     -> exitEdhTx exit $ EdhString $ procedureName pd
    EdhPrducr !pd     -> exitEdhTx exit $ EdhString $ procedureName pd


-- | utility dict(***apk,**kwargs,*args) - dict constructor by arguments
-- can be used to convert arguments pack into dict
dictProc :: EdhHostProc
dictProc (ArgsPack !args !kwargs) !exit = do
  !ets <- ask
  do
    !ds <-
      iopdFromList
        $ [ (EdhDecimal (fromIntegral i), t)
          | (i, t) <- zip [(0 :: Int) ..] args
          ]
    flip iopdUpdate ds $ (<$> odToList kwargs) $ \(key, val) ->
      (attrKeyValue key, val)
    u <- unsafeIOToSTM newUnique
    exitEdhSTM ets exit (EdhDict (Dict u ds))

dictSizeProc :: EdhHostProc
dictSizeProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
  throwEdhTx EvalError "bug: __DictType_size__ got kwargs"
dictSizeProc (ArgsPack [EdhDict (Dict _ !ds)] _) !exit = do
  !ets <- ask
  exitEdhSTM ets exit . EdhDecimal . fromIntegral =<< iopdSize ds
dictSizeProc _ _ =
  throwEdhTx EvalError "bug: __DictType_size__ got unexpected args"


listPushProc :: EdhHostProc
listPushProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
  throwEdhTx EvalError "bug: __ListType_push__ got kwargs"
listPushProc (ArgsPack [l@(EdhList (List _ !lv))] _) !exit = do
  !ets <- ask
  contEdhSTM
    $   mkHostProc (contextScope $ edh'context ets)
                   EdhMethod
                   "push"
                   listPush
                   (PackReceiver [RecvRestPosArgs "values"])
    >>= \mth -> exitEdhSTM ets exit mth
 where
  listPush :: EdhHostProc
  listPush (ArgsPack !args !kwargs') !exit' | odNull kwargs' = ask >>= \ets ->
    do
      modifyTVar' lv (args ++)
      exitEdhSTM ets exit' l
  listPush _ _ = throwEdhTx UsageError "invalid args to list.push()"
listPushProc _ _ =
  throwEdhTx EvalError "bug: __ListType_push__ got unexpected args"

listPopProc :: EdhHostProc
listPopProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
  throwEdhTx EvalError "bug: __ListType_pop__ got kwargs"
listPopProc (ArgsPack [EdhList (List _ !lv)] _) !exit = do
  !ets <- ask
  contEdhSTM
    $   mkHostProc (contextScope $ edh'context ets)
                   EdhMethod
                   "pop"
                   listPop
                   (PackReceiver [optionalArg "default" $ IntplSubs edhNone])
    >>= \mth -> exitEdhSTM ets exit mth
 where
  listPop :: EdhHostProc
  listPop !apk !exit' = case parseArgsPack edhNone parseArgs apk of
    Left  err     -> throwEdhTx UsageError err
    Right !defVal -> ask >>= \ets -> readTVar lv >>= \case
      (val : rest) -> writeTVar lv rest >> exitEdhSTM ets exit' val
      _            -> exitEdhSTM ets exit' defVal
   where
    parseArgs = ArgsPackParser [\arg _ -> Right arg]
      $ Map.fromList [("default", \arg _ -> Right arg)]
listPopProc _ _ =
  throwEdhTx EvalError "bug: __ListType_pop__ got unexpected args"


-- | operator (?<=) - element-of tester
elemProc :: EdhIntrinsicOp
elemProc !lhExpr !rhExpr !exit = do
  !ets <- ask
  evalExpr lhExpr $ \ !lhVal -> evalExpr rhExpr $ \ !rhVal ->
    case edhUltimate rhVal of
      EdhArgsPack (ArgsPack !vs _) ->
        exitEdhTx exit (EdhBool $ lhVal `elem` vs)
      EdhList (List _ !l) -> do
        ll <- readTVar l
        exitEdhSTM ets exit $ EdhBool $ lhVal `elem` ll
      EdhDict (Dict _ !ds) -> iopdLookup lhVal ds >>= \case
        Nothing -> exitEdhSTM ets exit $ EdhBool False
        Just _  -> exitEdhSTM ets exit $ EdhBool True
      _ -> exitEdhTx exit EdhContinue


-- | operator (|*) - prefix tester
isPrefixOfProc :: EdhIntrinsicOp
isPrefixOfProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  edhValueStr (edhUltimate lhVal) $ \lhRepr -> case lhRepr of
    EdhString !lhStr -> evalExpr rhExpr $ \ !rhVal ->
      edhValueStr (edhUltimate rhVal) $ \ !rhRepr -> case rhRepr of
        EdhString !rhStr ->
          exitEdhTx exit $ EdhBool $ lhStr `T.isPrefixOf` rhStr
        _ -> error "bug: edhValueStr returned non-string"
    _ -> error "bug: edhValueStr returned non-string"

-- | operator (*|) - suffix tester
hasSuffixProc :: EdhIntrinsicOp
hasSuffixProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  edhValueStr (edhUltimate lhVal) $ \lhRepr -> case lhRepr of
    EdhString !lhStr -> evalExpr rhExpr $ \ !rhVal ->
      edhValueStr (edhUltimate rhVal) $ \ !rhRepr -> case rhRepr of
        EdhString !rhStr ->
          exitEdhTx exit $ EdhBool $ rhStr `T.isSuffixOf` lhStr
        _ -> error "bug: edhValueStr returned non-string"
    _ -> error "bug: edhValueStr returned non-string"


-- | operator (=>) - prepender
prpdProc :: EdhIntrinsicOp
prpdProc !lhExpr !rhExpr !exit = do
  !ets <- ask
  evalExpr lhExpr $ \ !lhV ->
    let !lhVal = edhDeCaseClose lhV
    in  evalExpr rhExpr $ \ !rhVal -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !vs !kwargs) ->
            exitEdhTx exit (EdhArgsPack $ ArgsPack (lhVal : vs) kwargs)
          EdhList (List _ !l) -> do
            modifyTVar' l (lhVal :)
            exitEdhSTM ets exit rhVal
          EdhDict (Dict _ !ds) -> val2DictEntry ets lhVal $ \(k, v) -> do
            setDictItem k v ds
            exitEdhSTM ets exit rhVal
          _ -> exitEdhTx exit EdhContinue


-- | operator (>>) - list reverse prepender
lstrvrsPrpdProc :: EdhIntrinsicOp
lstrvrsPrpdProc !lhExpr !rhExpr !exit = do
  !ets <- ask
  evalExpr lhExpr $ \ !lhVal -> case edhUltimate lhVal of
    EdhList (List _ !ll) -> evalExpr rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhArgsPack (ArgsPack !vs !kwargs) -> do
          lll <- readTVar ll
          exitEdhSTM ets exit $ EdhArgsPack $ ArgsPack (reverse lll ++ vs)
                                                       kwargs
        EdhList (List _ !l) -> do
          lll <- readTVar ll
          modifyTVar' l (reverse lll ++)
          exitEdhSTM ets exit rhVal
        _ -> exitEdhTx exit EdhContinue
    _ -> exitEdhTx exit EdhContinue


-- | operator (=<) - comprehension maker, appender
--  * list comprehension:
--     [] =< for x from range(10) do x*x
--  * dict comprehension:
--     {} =< for x from range(10) do (x, x*x)
--  * tuple comprehension:
--     (,) =< for x from range(10) do x*x
--  * list append
--      [] =< (...) / [...] / {...}
--  * dict append
--      {} =< (...) / [...] / {...}
--  * tuple append
--      (,) =< (...) / [...] / {...}
cprhProc :: EdhIntrinsicOp
cprhProc !lhExpr !rhExpr !exit = do
  !ets <- ask
  let insertToDict :: EdhValue -> DictStore -> STM ()
      insertToDict !p !d = val2DictEntry ets p $ \(k, v) -> setDictItem k v d
  case rhExpr of
    ForExpr argsRcvr iterExpr doExpr -> evalExpr lhExpr $ \ !lhVal ->
      case edhUltimate lhVal of
        EdhList (List _ !l) -> edhForLoop
          ets
          argsRcvr
          iterExpr
          doExpr
          (\val -> modifyTVar' l (++ [val]))
          (\mkLoop -> runEdhTx ets $ mkLoop $ \_ -> exitEdhTx exit lhVal)
        EdhDict (Dict _ !d) -> edhForLoop
          ets
          argsRcvr
          iterExpr
          doExpr
          (\val -> insertToDict val d)
          (\mkLoop -> runEdhTx ets $ mkLoop $ \_ -> exitEdhTx exit lhVal)
        EdhArgsPack (ArgsPack !args !kwargs) -> do
          !posArgs <- newTVar args
          !kwArgs  <- iopdFromList $ odToList kwargs
          edhForLoop
              ets
              argsRcvr
              iterExpr
              doExpr
              (\val -> case val of
                EdhArgsPack (ArgsPack !args' !kwargs') -> do
                  modifyTVar' posArgs (++ args')
                  iopdUpdate (odToList kwargs') kwArgs
                _ -> modifyTVar' posArgs (++ [val])
              )
            $ \mkLoop -> runEdhTx ets $ mkLoop $ \_ -> do
                args'   <- readTVar posArgs
                kwargs' <- iopdSnapshot kwArgs
                exitEdhSTM ets exit (EdhArgsPack $ ArgsPack args' kwargs')
        _ ->
          throwEdhTx EvalError
            $  "don't know how to comprehend into a "
            <> T.pack (edhTypeNameOf lhVal)
            <> ": "
            <> T.pack (show lhVal)
    _ -> evalExpr lhExpr $ \ !lhVal -> evalExpr rhExpr $ \ !rhVal ->
      case edhUltimate lhVal of
        EdhArgsPack (ArgsPack !vs !kwvs) -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !args !kwargs) -> do
            kwIOPD <- iopdFromList $ odToList kwvs
            iopdUpdate (odToList kwargs) kwIOPD
            kwargs' <- iopdSnapshot kwIOPD
            exitEdhSTM ets exit (EdhArgsPack $ ArgsPack (vs ++ args) kwargs')
          EdhList (List _ !l) -> do
            ll <- readTVar l
            exitEdhSTM ets exit (EdhArgsPack $ ArgsPack (vs ++ ll) kwvs)
          EdhDict (Dict _ !ds) -> dictEntryList ds >>= \ !del ->
            exitEdhSTM ets exit (EdhArgsPack $ ArgsPack (vs ++ del) kwvs)
          _ -> exitEdhTx exit EdhContinue
        EdhList (List _ !l) -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !args _) -> do
            modifyTVar' l (++ args)
            exitEdhSTM ets exit lhVal
          EdhList (List _ !l') -> do
            ll <- readTVar l'
            modifyTVar' l (++ ll)
            exitEdhSTM ets exit lhVal
          EdhDict (Dict _ !ds) -> dictEntryList ds >>= \ !del -> do
            modifyTVar' l (++ del)
            exitEdhSTM ets exit lhVal
          _ -> exitEdhTx exit EdhContinue
        EdhDict (Dict _ !ds) -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack _ !kwargs) -> do
            iopdUpdate [ (attrKeyValue k, v) | (k, v) <- odToList kwargs ] ds
            exitEdhSTM ets exit lhVal
          EdhList (List _ !l) -> do
            ll <- readTVar l
            pvlToDictEntries ets ll $ \ !del -> do
              iopdUpdate del ds
              exitEdhSTM ets exit lhVal
          EdhDict (Dict _ !ds') -> do
            flip iopdUpdate ds =<< iopdToList ds'
            exitEdhSTM ets exit lhVal
          _ -> exitEdhTx exit EdhContinue
        _ -> exitEdhTx exit EdhContinue


-- | operator (<-) - event publisher
evtPubProc :: EdhIntrinsicOp
evtPubProc !lhExpr !rhExpr !exit = do
  !ets <- ask
  evalExpr lhExpr $ \ !lhVal -> case edhUltimate lhVal of
    EdhSink !es -> evalExpr rhExpr $ \ !rhV ->
      let !rhVal = edhDeCaseClose rhV
      in  do
            publishEvent es rhVal
            exitEdhSTM ets exit rhVal
    _ -> exitEdhTx exit EdhContinue

