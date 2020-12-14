module Language.Edh.Batteries.Data where

-- import           Debug.Trace

import Control.Concurrent.STM
  ( STM,
    modifyTVar',
    newTVar,
    readTVar,
    writeTVar,
  )
import Control.Monad.Reader
  ( unless,
    when,
  )
import qualified Data.Bits as Bits
import Data.ByteString (ByteString)
import Data.Lossless.Decimal as D (Decimal, nan)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.UUID as UUID
import Data.Unique (hashUnique, newUnique)
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Args
import Language.Edh.Control
  ( EdhErrorTag (EvalError, UsageError),
    noSrcRange,
  )
import Language.Edh.CoreLang (lookupEdhObjMagic)
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.InterOp (mkHostProc')
import Language.Edh.RtTypes
import Language.Edh.Utils (seqcontSTM)
import Prelude

strEncodeProc :: Text -> EdhHostProc
strEncodeProc !str !exit = exitEdhTx exit $ EdhBlob $ TE.encodeUtf8 str

blobDecodeProc :: ByteString -> EdhHostProc
blobDecodeProc !blob !exit = exitEdhTx exit $ EdhString $ TE.decodeUtf8 blob

blobProc :: EdhValue -> RestKwArgs -> EdhHostProc
blobProc !val !kwargs !exit !ets = case edhUltimate val of
  b@EdhBlob {} -> exitEdh ets exit b
  (EdhString !str) -> exitEdh ets exit $ EdhBlob $ TE.encodeUtf8 str
  (EdhObject !o) ->
    lookupEdhObjMagic o (AttrByName "__blob__") >>= \case
      (_, EdhNil) -> naExit
      (!this', EdhProcedure (EdhMethod !mth) _) ->
        runEdhTx ets $
          callEdhMethod this' o mth (ArgsPack [] kwargs) id chkMagicRtn
      (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
        runEdhTx ets $
          callEdhMethod this that mth (ArgsPack [] kwargs) id chkMagicRtn
      (_, !badMagic) ->
        throwEdh ets UsageError $
          "bad magic __blob__ of "
            <> edhTypeNameOf badMagic
            <> " on class "
            <> objClassName o
  _ -> naExit
  where
    chkMagicRtn !rtn _ets = case edhUltimate rtn of
      EdhDefault _ !exprDef !etsDef ->
        runEdhTx (fromMaybe ets etsDef) $
          evalExpr (deExpr' exprDef) $
            \ !defVal _ets -> case defVal of
              EdhNil -> naExit
              _ -> exitEdh ets exit defVal
      _ -> exitEdh ets exit rtn
    naExit = case odLookup (AttrByName "orElse") kwargs of
      Just !altVal -> exitEdh ets exit altVal
      Nothing -> edhValueDesc ets val $ \ !badDesc ->
        throwEdh ets UsageError $ "not convertible to blob: " <> badDesc

propertyProc :: EdhValue -> Maybe EdhValue -> EdhHostProc
propertyProc !getterVal !setterVal !exit !ets =
  case edh'obj'store caller'this of
    ClassStore !cls -> defProp (edh'class'store cls)
    HashStore !hs -> defProp hs
    _ -> throwEdh ets UsageError "can not define property for a host object"
  where
    !ctx = edh'context ets
    !caller'this = edh'scope'this $ callingScope ctx

    defProp :: EntityStore -> STM ()
    defProp !es = withGetter $ \ !getter -> withSetter $ \ !setter -> do
      let !pd = EdhProcedure (EdhDescriptor getter setter) Nothing
          !name = edh'procedure'name getter
      when (name /= AttrByName "_") $
        unless (edh'ctx'pure ctx) $
          iopdInsert
            name
            pd
            es
      exitEdh ets exit pd

    withGetter :: (ProcDefi -> STM ()) -> STM ()
    withGetter getterExit = case getterVal of
      EdhProcedure (EdhMethod !getter) _ -> getterExit getter
      -- todo is this right? to unbind a bound method to define a new prop
      EdhBoundProc (EdhMethod !getter) _ _ _ -> getterExit getter
      !badVal ->
        throwEdh ets UsageError $
          "need a method procedure to define a property, not a: "
            <> edhTypeNameOf badVal
    withSetter :: (Maybe ProcDefi -> STM ()) -> STM ()
    withSetter setterExit = case setterVal of
      Nothing -> setterExit Nothing
      Just (EdhProcedure (EdhMethod !setter) _) -> setterExit $ Just setter
      -- todo is this right? to unbind a bound method to define a new prop
      Just (EdhBoundProc (EdhMethod !setter) _ _ _) -> setterExit $ Just setter
      Just !badVal ->
        throwEdh ets UsageError $
          "need a method procedure to define a property, not a: "
            <> edhTypeNameOf badVal

setterProc :: EdhValue -> EdhHostProc
setterProc !setterVal !exit !ets = case edh'obj'store caller'this of
  ClassStore !cls -> defProp (edh'class'store cls)
  HashStore !hs -> defProp hs
  _ -> throwEdh ets UsageError "can not define property for a host object"
  where
    !ctx = edh'context ets
    !caller'this = edh'scope'this $ callingScope ctx

    defProp :: EntityStore -> STM ()
    defProp !es = case setterVal of
      EdhProcedure (EdhMethod !setter) _ -> findGetter es setter
      EdhBoundProc (EdhMethod !setter) _ _ _ -> findGetter es setter
      !badSetter -> edhValueDesc ets badSetter $
        \ !badDesc -> throwEdh ets UsageError $ "invalid setter: " <> badDesc

    findGetter :: EntityStore -> ProcDefi -> STM ()
    findGetter !es !setter =
      iopdLookup name es >>= \case
        Just (EdhProcedure (EdhDescriptor !getter _) _) ->
          setSetter es setter getter
        Just (EdhBoundProc (EdhDescriptor !getter _) _ _ _) ->
          setSetter es setter getter
        _ ->
          throwEdh ets UsageError $ "missing property getter " <> T.pack (show name)
      where
        !name = edh'procedure'name setter

    setSetter :: EntityStore -> ProcDefi -> ProcDefi -> STM ()
    setSetter !es !setter !getter = do
      let !pd = EdhProcedure (EdhDescriptor getter $ Just setter) Nothing
      unless (edh'ctx'pure ctx) $ iopdInsert name pd es
      exitEdh ets exit pd
      where
        !name = edh'procedure'name setter

-- | operator (@) - attribute key dereferencing
attrDerefAddrProc :: EdhIntrinsicOp
attrDerefAddrProc !lhExpr !rhExpr !exit =
  evalExprSrc rhExpr $ \ !rhVal !ets ->
    let naExit = edhValueDesc ets rhVal $ \ !badRefDesc ->
          throwEdh ets EvalError $
            "invalid attribute reference value: "
              <> badRefDesc
     in edhValueAsAttrKey' ets rhVal naExit $ \ !key ->
          runEdhTx ets $ getEdhAttr lhExpr key (noAttr $ attrKeyStr key) exit
  where
    noAttr !keyRepr !lhVal !ets = edhValueDesc ets lhVal $ \ !badDesc ->
      throwEdh ets EvalError $
        "no such attribute `"
          <> keyRepr
          <> "` from a "
          <> badDesc

-- | operator (?@) - attribute dereferencing tempter,
-- address an attribute off an object if possible, nil otherwise
attrDerefTemptProc :: EdhIntrinsicOp
attrDerefTemptProc !lhExpr !rhExpr !exit =
  evalExprSrc rhExpr $ \ !rhVal !ets ->
    let naExit = edhValueDesc ets rhVal $ \ !badRefDesc ->
          throwEdh ets EvalError $
            "invalid attribute reference value: "
              <> badRefDesc
     in edhValueAsAttrKey' ets rhVal naExit $
          \ !key -> runEdhTx ets $ getEdhAttr lhExpr key noAttr exit
  where
    noAttr _ = exitEdhTx exit nil

-- | operator (?) - attribute tempter,
-- address an attribute off an object if possible, nil otherwise
attrTemptProc :: EdhIntrinsicOp
attrTemptProc !lhExpr rhExpr@(ExprSrc !rhe _) !exit !ets = case rhe of
  AttrExpr (DirectRef (AttrAddrSrc !addr _)) ->
    resolveEdhAttrAddr ets addr $ \ !key ->
      runEdhTx ets $ getEdhAttr lhExpr key (const $ exitEdhTx exit nil) exit
  _ ->
    throwEdh ets EvalError $
      "invalid attribute expression: "
        <> T.pack
          (show rhExpr)

-- | operator ($) - low-precedence operator for procedure call
--
-- similar to the function application ($) operator in Haskell
-- can be used to apply decorators with nicer syntax
fapProc :: EdhIntrinsicOp
fapProc !lhExpr rhExpr@(ExprSrc !rhe _) !exit =
  evalExprSrc lhExpr $ \ !lhVal -> case edhUltimate lhVal of
    -- special case, support merging of apks with func app syntax, so args can
    -- be chained then applied to some function
    EdhArgsPack (ArgsPack !args !kwargs) -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhArgsPack (ArgsPack !args' !kwargs') -> \ !ets -> do
          !kwIOPD <- iopdFromList $ odToList kwargs
          iopdUpdate (odToList kwargs') kwIOPD
          !kwargs'' <- iopdSnapshot kwIOPD
          exitEdh ets exit $ EdhArgsPack $ ArgsPack (args ++ args') kwargs''
        _ -> exitEdhTx exit $ EdhArgsPack $ ArgsPack (args ++ [rhVal]) kwargs
    -- normal case
    !calleeVal -> \ !ets -> edhPrepareCall ets calleeVal argsPkr $
      \ !mkCall -> runEdhTx ets (mkCall exit)
  where
    argsPkr :: ArgsPacker
    argsPkr = case rhe of
      ArgsPackExpr !pkr -> pkr
      _ -> [SendPosArg rhExpr]

-- | operator (|) - flipped ($), low-precedence operator for procedure call
--
-- sorta similar to UNIX pipe
ffapProc :: EdhIntrinsicOp
ffapProc !lhExpr !rhExpr = fapProc rhExpr lhExpr

-- | operator (:=) - named value definition
defProc :: EdhIntrinsicOp
defProc (ExprSrc (AttrExpr (DirectRef (AttrAddrSrc (NamedAttr !valName) _))) _) !rhExpr !exit =
  evalExprSrc rhExpr $ \ !rhVal !ets -> do
    let !ctx = edh'context ets
        !scope = contextScope ctx
        !es = edh'scope'entity scope
        !key = AttrByName valName
        !rhv = edhDeCaseWrap rhVal
        !nv = EdhNamedValue valName rhv
        doAssign = do
          iopdInsert key nv es
          defineScopeAttr ets key nv
    iopdLookup key es >>= \case
      Nothing -> do
        doAssign
        exitEdh ets exit nv
      Just oldDef@(EdhNamedValue !n !v) ->
        if v /= rhv
          then edhValueRepr ets rhv $ \ !newRepr ->
            edhValueRepr ets oldDef $ \ !oldRepr ->
              throwEdh ets EvalError $
                "can not redefine "
                  <> valName
                  <> " from { "
                  <> oldRepr
                  <> " } to { "
                  <> newRepr
                  <> " }"
          else do
            -- avoid writing the entity if all same
            unless (n == valName) doAssign
            exitEdh ets exit nv
      _ -> do
        doAssign
        exitEdh ets exit nv
defProc !lhExpr _ _ =
  throwEdhTx EvalError $ "invalid value definition: " <> T.pack (show lhExpr)

-- | operator (?:=) - named value definition if missing
defMissingProc :: EdhIntrinsicOp
defMissingProc (ExprSrc (AttrExpr (DirectRef (AttrAddrSrc (NamedAttr "_") _))) _) _ _ !ets =
  throwEdh ets UsageError "not so reasonable: _ ?:= xxx"
defMissingProc (ExprSrc (AttrExpr (DirectRef (AttrAddrSrc (NamedAttr !valName) _))) _) !rhExpr !exit !ets =
  iopdLookup key es >>= \case
    Nothing -> runEdhTx ets $
      evalExprSrc rhExpr $ \ !rhVal _ets -> do
        let !rhv = edhDeCaseWrap rhVal
            !nv = EdhNamedValue valName rhv
        iopdInsert key nv es
        defineScopeAttr ets key nv
        exitEdh ets exit nv
    Just !preVal -> exitEdh ets exit preVal
  where
    !es = edh'scope'entity $ contextScope $ edh'context ets
    !key = AttrByName valName
defMissingProc !lhExpr _ _ !ets =
  throwEdh ets EvalError $ "invalid value definition: " <> T.pack (show lhExpr)

-- | operator (:) - pair constructor
pairCtorProc :: EdhIntrinsicOp
pairCtorProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $ \ !rhVal ->
    exitEdhTx exit (EdhPair (edhDeCaseWrap lhVal) (edhDeCaseWrap rhVal))

-- todo support more forms of UUID ctor args
uuidCtorProc :: Maybe Text -> EdhHostProc
uuidCtorProc Nothing !exit !ets = mkUUID >>= exitEdh ets exit . EdhUUID
uuidCtorProc (Just !uuidTxt) !exit !ets = case UUID.fromText uuidTxt of
  Just !uuid -> exitEdh ets exit $ EdhUUID uuid
  _ -> throwEdh ets UsageError $ "invalid uuid string: " <> uuidTxt

apkArgsProc :: ArgsPack -> EdhHostProc
apkArgsProc (ArgsPack _ !kwargs) _
  | not $ odNull kwargs =
    throwEdhTx EvalError "bug: __ArgsPackType_args__ got kwargs"
apkArgsProc (ArgsPack [EdhArgsPack (ArgsPack !args _)] _) !exit =
  exitEdhTx exit $ EdhArgsPack $ ArgsPack args odEmpty
apkArgsProc _ _ =
  throwEdhTx EvalError "bug: __ArgsPackType_args__ got unexpected args"

apkKwrgsProc :: ArgsPack -> EdhHostProc
apkKwrgsProc (ArgsPack _ !kwargs) _
  | not $ odNull kwargs =
    throwEdhTx EvalError "bug: __ArgsPackType_kwargs__ got kwargs"
apkKwrgsProc (ArgsPack [EdhArgsPack (ArgsPack _ !kwargs')] _) !exit =
  exitEdhTx exit $ EdhArgsPack $ ArgsPack [] kwargs'
apkKwrgsProc _ _ =
  throwEdhTx EvalError "bug: __ArgsPackType_kwargs__ got unexpected args"

-- | utility id(val) -- obtain unique evident value of a value
--
-- this follows the semantic of Python's `id` function for object values and
-- a few other types, notably including event sink values;
-- and for values of immutable types, this follows the semantic of Haskell to
-- just return the value itself.
--
-- but unlike Python's `id` function which returns integers, here we return
-- `UUID`s for objects et al.
--
-- this is useful e.g. in log records you have no other way to write
-- information about an event sink, so that it can be evident whether the sink
-- is the same as appeared in another log record. as `repr` of an event sink
-- is always '<sink>'. though it's not a problem when you have those values
-- pertaining to an interactive repl session, where `is` operator can easily
-- tell you that.
--
-- todo
--   *) hashUnique doesn't guarantee free of collision, better impl?
idProc :: EdhValue -> EdhHostProc
idProc !val !exit = exitEdhTx exit $ identityOf val
  where
    idFromInt :: Int -> EdhValue
    idFromInt !i =
      EdhUUID $
        UUID.fromWords
          0xcafe
          0xface
          (fromIntegral $ Bits.shiftR i 32)
          (fromIntegral i)

    identityOf :: EdhValue -> EdhValue
    identityOf (EdhObject !o) = idOfObj o
    identityOf (EdhSink !s) = idFromInt $ hashUnique $ evs'uniq s
    identityOf (EdhNamedValue !n !v) = EdhNamedValue n (identityOf v)
    identityOf (EdhPair !l !r) = EdhPair (identityOf l) (identityOf r)
    identityOf (EdhDict (Dict !u _)) = idFromInt $ hashUnique u
    identityOf (EdhList (List !u _)) = idFromInt $ hashUnique u
    identityOf (EdhProcedure !p _) = idOfProc p
    identityOf (EdhBoundProc !p !this !that _) =
      EdhPair (EdhPair (idOfProc p) (idOfObj this)) (idOfObj that)
    identityOf (EdhExpr !u _ _) = idFromInt $ hashUnique u
    identityOf (EdhArgsPack (ArgsPack !args !kwargs)) =
      go
        args
        (odToList kwargs)
        []
        []
      where
        go ::
          [EdhValue] ->
          [(AttrKey, EdhValue)] ->
          [EdhValue] ->
          [(AttrKey, EdhValue)] ->
          EdhValue
        go [] [] !idArgs !idKwArgs =
          EdhArgsPack $ ArgsPack (reverse idArgs) (odFromList $ reverse idKwArgs)
        go [] ((!k, !v) : restKwArgs) !idArgs !idKwArgs =
          go [] restKwArgs idArgs ((k, identityOf v) : idKwArgs)
        go (v : restArgs) !kwargs' !idArgs !idKwArgs =
          go restArgs kwargs' (identityOf v : idArgs) idKwArgs
    identityOf !v = v

    idOfObj :: Object -> EdhValue
    idOfObj o = idFromInt $ hashUnique $ edh'obj'ident o

    idOfProcDefi :: ProcDefi -> EdhValue
    idOfProcDefi !def = idFromInt $ hashUnique $ edh'procedure'ident def

    idOfProc :: EdhProcDefi -> EdhValue
    idOfProc (EdhIntrOp _ _ !def) =
      idFromInt $ hashUnique $ intrinsic'op'uniq def
    idOfProc (EdhOprtor _ _ _ !def) = idOfProcDefi def
    idOfProc (EdhMethod !def) = idOfProcDefi def
    idOfProc (EdhGnrtor !def) = idOfProcDefi def
    idOfProc (EdhIntrpr !def) = idOfProcDefi def
    idOfProc (EdhPrducr !def) = idOfProcDefi def
    idOfProc (EdhDescriptor !getter !maybeSetter) = case maybeSetter of
      Nothing -> idOfProcDefi getter
      Just !setter -> EdhPair (idOfProcDefi getter) (idOfProcDefi setter)

-- | utility str(*args,**kwargs) - convert to string
strProc :: ArgsPack -> EdhHostProc
strProc (ArgsPack !args !kwargs) !exit !ets = go [] [] args (odToList kwargs)
  where
    go ::
      [EdhValue] ->
      [(AttrKey, EdhValue)] ->
      [EdhValue] ->
      [(AttrKey, EdhValue)] ->
      STM ()
    go [str] kwStrs [] [] | null kwStrs = exitEdh ets exit str
    go strs kwStrs [] [] =
      exitEdh ets exit $ EdhArgsPack $ ArgsPack (reverse strs) $ odFromList kwStrs
    go strs kwStrs (v : rest) kwps =
      edhValueStr ets v $ \ !s -> go (EdhString s : strs) kwStrs rest kwps
    go strs kwStrs [] ((k, v) : rest) =
      edhValueStr ets v $ \ !s -> go strs ((k, EdhString s) : kwStrs) [] rest

-- | utility json() - convert the args to json string
jsonProc :: ArgsPack -> EdhHostProc
jsonProc (ArgsPack [value] !kwargs) !exit !ets
  | odNull kwargs =
    edhValueJson ets value $ exitEdh ets exit . EdhString
jsonProc !apk !exit !ets =
  edhValueJson ets (EdhArgsPack apk) $ exitEdh ets exit . EdhString

-- | operator (++) - string coercing concatenator
concatProc :: EdhIntrinsicOp
concatProc !lhExpr !rhExpr !exit !ets =
  runEdhTx ets $
    evalExprSrc lhExpr $ \ !lhVal ->
      evalExprSrc rhExpr $ \ !rhVal -> case edhUltimate lhVal of
        EdhString !lhStr -> case edhUltimate rhVal of
          EdhString !rhStr -> exitEdhTx exit $ EdhString $ lhStr <> rhStr
          _ -> \_ets -> defaultConvert lhVal rhVal
        EdhBlob !lhBlob -> case edhUltimate rhVal of
          EdhBlob !rhBlob -> exitEdhTx exit $ EdhBlob $ lhBlob <> rhBlob
          EdhString !rhStr ->
            exitEdhTx exit $ EdhBlob $ lhBlob <> TE.encodeUtf8 rhStr
          _ -> exitEdhTx exit edhNA
        _ -> \_ets -> defaultConvert lhVal rhVal
  where
    defaultConvert :: EdhValue -> EdhValue -> STM ()
    defaultConvert !lhVal !rhVal = do
      !u <- unsafeIOToSTM newUnique
      exitEdh ets exit $
        EdhDefault
          u
          ( InfixExpr
              "++"
              ( ExprSrc
                  ( CallExpr
                      ( ExprSrc
                          (AttrExpr (DirectRef (AttrAddrSrc (NamedAttr "str") noSrcRange)))
                          noSrcRange
                      )
                      [SendPosArg (ExprSrc (LitExpr (ValueLiteral lhVal)) noSrcRange)]
                  )
                  noSrcRange
              )
              ( ExprSrc
                  ( CallExpr
                      ( ExprSrc
                          (AttrExpr (DirectRef (AttrAddrSrc (NamedAttr "str") noSrcRange)))
                          noSrcRange
                      )
                      [SendPosArg (ExprSrc (LitExpr (ValueLiteral rhVal)) noSrcRange)]
                  )
                  noSrcRange
              )
          )
          (Just ets)

-- | utility repr(*args,**kwargs) - repr extractor
reprProc :: ArgsPack -> EdhHostProc
reprProc (ArgsPack !args !kwargs) !exit !ets = go [] [] args (odToList kwargs)
  where
    go ::
      [EdhValue] ->
      [(AttrKey, EdhValue)] ->
      [EdhValue] ->
      [(AttrKey, EdhValue)] ->
      STM ()
    go [repr] kwReprs [] [] | null kwReprs = exitEdh ets exit repr
    go reprs kwReprs [] [] =
      exitEdh ets exit $
        EdhArgsPack $
          ArgsPack (reverse reprs) $
            odFromList
              kwReprs
    go reprs kwReprs (v : rest) kwps =
      edhValueRepr ets v $ \ !r -> go (EdhString r : reprs) kwReprs rest kwps
    go reprs kwReprs [] ((k, v) : rest) =
      edhValueRepr ets v $ \ !r -> go reprs ((k, EdhString r) : kwReprs) [] rest

capProc :: EdhValue -> RestKwArgs -> EdhHostProc
capProc !v !kwargs !exit !ets = case edhUltimate v of
  EdhObject !o ->
    lookupEdhObjMagic o (AttrByName "__cap__") >>= \case
      (_, EdhNil) -> exitEdh ets exit $ EdhDecimal D.nan
      (!this', EdhProcedure (EdhMethod !mth) _) ->
        runEdhTx ets $ callEdhMethod this' o mth (ArgsPack [] kwargs) id exit
      (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
        runEdhTx ets $ callEdhMethod this that mth (ArgsPack [] kwargs) id exit
      (_, !badMagic) ->
        throwEdh ets UsageError $
          "bad magic __cap__ of "
            <> edhTypeNameOf badMagic
            <> " on class "
            <> objClassName o
  _ -> exitEdh ets exit $ EdhDecimal D.nan

growProc :: EdhValue -> Decimal -> RestKwArgs -> EdhHostProc
growProc !v !newCap !kwargs !exit !ets = case edhUltimate v of
  EdhObject !o ->
    lookupEdhObjMagic o (AttrByName "__grow__") >>= \case
      (_, EdhNil) ->
        throwEdh ets UsageError $
          "grow() not supported by the object of class "
            <> objClassName o
      (!this', EdhProcedure (EdhMethod !mth) _) ->
        runEdhTx ets $
          callEdhMethod
            this'
            o
            mth
            (ArgsPack [EdhDecimal newCap] kwargs)
            id
            exit
      (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
        runEdhTx ets $
          callEdhMethod
            this
            that
            mth
            (ArgsPack [EdhDecimal newCap] kwargs)
            id
            exit
      (_, !badMagic) ->
        throwEdh ets UsageError $
          "bad magic __grow__ of "
            <> edhTypeNameOf badMagic
            <> " on class "
            <> objClassName o
  !badVal -> edhValueDesc ets badVal $ \ !badDesc ->
    throwEdh ets UsageError $ "grow() not supported by: " <> badDesc

lenProc :: EdhValue -> RestKwArgs -> EdhHostProc
lenProc !v !kwargs !exit !ets = case edhUltimate v of
  EdhObject !o ->
    lookupEdhObjMagic o (AttrByName "__len__") >>= \case
      (_, EdhNil) -> exitEdh ets exit $ EdhDecimal D.nan
      (!this', EdhProcedure (EdhMethod !mth) _) ->
        runEdhTx ets $ callEdhMethod this' o mth (ArgsPack [] kwargs) id exit
      (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
        runEdhTx ets $ callEdhMethod this that mth (ArgsPack [] kwargs) id exit
      (_, !badMagic) ->
        throwEdh ets UsageError $
          "bad magic __len__ of "
            <> edhTypeNameOf badMagic
            <> " on class "
            <> objClassName o
  EdhList (List _ !lv) ->
    length <$> readTVar lv >>= \ !llen ->
      exitEdh ets exit $ EdhDecimal $ fromIntegral llen
  EdhDict (Dict _ !ds) ->
    iopdSize ds
      >>= \ !dlen -> exitEdh ets exit $ EdhDecimal $ fromIntegral dlen
  EdhArgsPack (ArgsPack !posArgs !kwArgs)
    | odNull kwArgs ->
      -- no keyword arg, assuming tuple semantics
      exitEdh ets exit $ EdhDecimal $ fromIntegral $ length posArgs
  EdhArgsPack (ArgsPack !posArgs !kwArgs)
    | null posArgs ->
      -- no positional arg, assuming named tuple semantics
      exitEdh ets exit $ EdhDecimal $ fromIntegral $ odSize kwArgs
  EdhArgsPack {} ->
    throwEdh
      ets
      UsageError
      "unresonable to get length of an apk with both positional and keyword args"
  _ -> exitEdh ets exit $ EdhDecimal D.nan

markProc :: EdhValue -> Decimal -> RestKwArgs -> EdhHostProc
markProc !v !newLen !kwargs !exit !ets = case edhUltimate v of
  EdhObject !o ->
    lookupEdhObjMagic o (AttrByName "__mark__") >>= \case
      (_, EdhNil) ->
        throwEdh ets UsageError $
          "mark() not supported by the object of class "
            <> objClassName o
      (!this', EdhProcedure (EdhMethod !mth) _) ->
        runEdhTx ets $
          callEdhMethod
            this'
            o
            mth
            (ArgsPack [EdhDecimal newLen] kwargs)
            id
            exit
      (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
        runEdhTx ets $
          callEdhMethod
            this
            that
            mth
            (ArgsPack [EdhDecimal newLen] kwargs)
            id
            exit
      (_, !badMagic) ->
        throwEdh ets UsageError $
          "bad magic __mark__ of "
            <> edhTypeNameOf badMagic
            <> " on class "
            <> objClassName o
  !badVal ->
    throwEdh ets UsageError $
      "mark() not supported by a value of " <> edhTypeNameOf badVal

showProc :: EdhValue -> RestKwArgs -> EdhHostProc
showProc (EdhArgsPack (ArgsPack [!v] !kwargs')) !kwargs !exit !ets
  | odNull kwargs = showProc v kwargs' exit ets
showProc !v !kwargs !exit !ets = case v of
  -- show of named value
  EdhNamedValue !n !val -> edhValueRepr ets val $
    \ !repr -> exitEdh ets exit $ EdhString $ n <> " := " <> repr <> ""
  -- show of other values
  _ -> case edhUltimate v of
    EdhObject !o -> case edh'obj'store o of
      ClassStore {} ->
        lookupEdhObjMagic (edh'obj'class o) (AttrByName "__show__")
          >>= showWithMagic o
      _ -> lookupEdhObjMagic o (AttrByName "__show__") >>= showWithMagic o
    EdhProcedure !callable Nothing ->
      exitEdh ets exit $ EdhString $ T.pack (show callable)
    EdhProcedure !callable Just {} ->
      exitEdh ets exit $ EdhString $ "effectful " <> T.pack (show callable)
    EdhBoundProc !callable _ _ Nothing ->
      exitEdh ets exit $ EdhString $ "bound " <> T.pack (show callable)
    EdhBoundProc !callable _ _ Just {} ->
      exitEdh ets exit $
        EdhString $
          "effectful bound "
            <> T.pack
              (show callable)
    -- todo specialize more informative show for intrinsic types of values
    _ -> showWithNoMagic
  where
    showWithMagic !o = \case
      (_, EdhNil) -> showWithNoMagic
      (!this', EdhProcedure (EdhMethod !mth) _) ->
        runEdhTx ets $ callEdhMethod this' o mth (ArgsPack [] kwargs) id exit
      (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
        runEdhTx ets $ callEdhMethod this that mth (ArgsPack [] kwargs) id exit
      (_, !badMagic) ->
        throwEdh ets UsageError $
          "bad magic __show__ of "
            <> edhTypeNameOf badMagic
            <> " on class "
            <> objClassName o
    showWithNoMagic = edhValueStr ets v $ \ !s ->
      exitEdh ets exit $ EdhString $ edhTypeNameOf v <> ": " <> s

descProc :: EdhValue -> RestKwArgs -> EdhHostProc
descProc (EdhArgsPack (ArgsPack [!v] !kwargs')) !kwargs !exit !ets
  | odNull kwargs = descProc v kwargs' exit ets
descProc !v !kwargs !exit !ets = case edhUltimate v of
  EdhObject !o -> case edh'obj'store o of
    ClassStore {} ->
      lookupEdhObjMagic (edh'obj'class o) (AttrByName "__desc__") >>= \case
        (_, EdhNil) -> exitEdh ets exit $ EdhString $ classDocString o
        !magicMth -> descWithMagic o magicMth
    _ -> lookupEdhObjMagic o (AttrByName "__desc__") >>= descWithMagic o
  EdhProcedure !callable Nothing ->
    exitEdh ets exit $
      EdhString $
        "It is a "
          <> T.pack (show callable)
          <> docString (callableDoc callable)
  EdhProcedure !callable Just {} ->
    exitEdh ets exit $
      EdhString $
        "It is an effectful "
          <> T.pack (show callable)
          <> docString (callableDoc callable)
  EdhBoundProc !callable _ _ Nothing ->
    exitEdh ets exit $
      EdhString $
        "It is a bound "
          <> T.pack (show callable)
          <> docString (callableDoc callable)
  EdhBoundProc !callable _ _ Just {} ->
    exitEdh ets exit $
      EdhString $
        "It is an effectful bound "
          <> T.pack (show callable)
          <> docString (callableDoc callable)
  _ ->
    edhValueDesc ets v $ \ !d -> exitEdh ets exit $ EdhString $ "It is a " <> d
  where
    docString :: Maybe DocComment -> Text
    -- todo process ReST formatting?
    docString !docCmt =
      maybe "" (("\n * doc comments *\n" <>) . T.unlines) docCmt

    classDocString :: Object -> Text
    classDocString !c = case edh'obj'store c of
      ClassStore (Class !cp _ _ _) ->
        "class "
          <> procedureName cp
          -- TODO show super classes it extends
          <> docString (edh'procedure'doc cp)
      -- TODO show member methods / properties / static attrs etc.
      _ -> "class " <> edhClassName c

    -- TODO specialize more informative description (statistical wise) for
    --      intrinsic types of values
    descWithMagic !o = \case
      (_, EdhNil) ->
        exitEdh ets exit $
          EdhString $
            "It is an object of "
              <> classDocString
                (edh'obj'class o)
      (!this', EdhProcedure (EdhMethod !mth) _) ->
        runEdhTx ets $ callEdhMethod this' o mth (ArgsPack [] kwargs) id exit
      (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
        runEdhTx ets $ callEdhMethod this that mth (ArgsPack [] kwargs) id exit
      (_, !badMagic) ->
        throwEdh ets UsageError $
          "bad magic __desc__ of "
            <> edhTypeNameOf badMagic
            <> " on class "
            <> objClassName o

-- | utility null(*args,**kwargs) - null tester
isNullProc :: ArgsPack -> EdhHostProc
isNullProc (ArgsPack !args !kwargs) !exit !ets =
  if odNull kwargs
    then case args of
      [v] -> edhValueNull ets v $ \ !isNull -> exitEdh ets exit $ EdhBool isNull
      _ -> seqcontSTM (edhValueNull ets <$> args) $ \ !argsNulls ->
        exitEdh ets exit $ EdhArgsPack $ ArgsPack (EdhBool <$> argsNulls) odEmpty
    else seqcontSTM (edhValueNull ets <$> args) $ \ !argsNulls ->
      seqcontSTM
        [ \ !exit' ->
            edhValueNull ets v (\ !isNull -> exit' (k, EdhBool isNull))
          | (k, v) <- odToList kwargs
        ]
        $ \ !kwargsNulls ->
          exitEdh
            ets
            exit
            ( EdhArgsPack $
                ArgsPack (EdhBool <$> argsNulls) (odFromList kwargsNulls)
            )

-- | utility compare(v1, v2) - value comparator
cmpProc :: EdhValue -> EdhValue -> EdhHostProc
cmpProc !v1 !v2 !exit !ets = edhCompareValue ets v1 v2 $ \case
  Nothing -> exitEdh ets exit edhNA
  Just !conclusion -> exitEdh ets exit $ EdhOrd conclusion

-- | utility type(*args,**kwargs) - value type introspector
typeProc :: ArgsPack -> EdhHostProc
typeProc (ArgsPack !args !kwargs) !exit =
  let !argsType = edhTypeValOf <$> args
   in if odNull kwargs
        then case argsType of
          [t] -> exitEdhTx exit t
          _ -> exitEdhTx exit $ EdhArgsPack $ ArgsPack argsType odEmpty
        else
          exitEdhTx
            exit
            (EdhArgsPack $ ArgsPack argsType $ odMap edhTypeValOf kwargs)
  where
    edhTypeValOf :: EdhValue -> EdhValue
    -- it's a taboo to get the type of a nil, either named or not
    edhTypeValOf EdhNil = edhNone
    edhTypeValOf (EdhNamedValue _n EdhNil) = edhNone
    edhTypeValOf v = EdhType $ edhTypeOf v

procNameProc :: EdhValue -> EdhHostProc
procNameProc !p !exit !ets = case p of
  EdhProcedure !callable _ -> cpName callable
  EdhBoundProc !callable _this _that _ -> cpName callable
  _ -> exitEdh ets exit nil
  where
    cpName :: EdhProcDefi -> STM ()
    cpName = \case
      EdhIntrOp _ _ (IntrinOpDefi _ !opSym _) ->
        exitEdh ets exit $ EdhString $ "(" <> opSym <> ")"
      EdhOprtor _ _ _ !pd -> exitEdh ets exit $ EdhString $ procedureName pd
      EdhMethod !pd -> exitEdh ets exit $ EdhString $ procedureName pd
      EdhGnrtor !pd -> exitEdh ets exit $ EdhString $ procedureName pd
      EdhIntrpr !pd -> exitEdh ets exit $ EdhString $ procedureName pd
      EdhPrducr !pd -> exitEdh ets exit $ EdhString $ procedureName pd
      EdhDescriptor !getter _setter ->
        exitEdh ets exit $ EdhString $ procedureName getter

-- | utility dict(***apk,**kwargs,*args) - dict constructor by arguments
-- can be used to convert arguments pack into dict
dictProc :: ArgsPack -> EdhHostProc
dictProc (ArgsPack !args !kwargs) !exit !ets = do
  !ds <-
    iopdFromList $
      [ (EdhDecimal (fromIntegral i), t)
        | (i, t) <- zip [(0 :: Int) ..] args
      ]
  flip iopdUpdate ds $
    (<$> odToList kwargs) $ \(key, val) -> (attrKeyValue key, val)
  !u <- unsafeIOToSTM newUnique
  exitEdh ets exit (EdhDict (Dict u ds))

dictSizeProc :: Dict -> EdhHostProc
dictSizeProc (Dict _ !ds) !exit !ets =
  exitEdh ets exit . EdhDecimal . fromIntegral =<< iopdSize ds

dictKeysProc :: Dict -> EdhHostProc
dictKeysProc (Dict _ !ds) !exit !ets =
  exitEdh ets exit . EdhArgsPack . flip ArgsPack odEmpty =<< iopdKeys ds

dictValuesProc :: Dict -> EdhHostProc
dictValuesProc (Dict _ !ds) !exit !ets =
  exitEdh ets exit . EdhArgsPack . flip ArgsPack odEmpty =<< iopdValues ds

listPushProc :: List -> EdhHostProc
listPushProc l@(List _ !lv) !exit !ets =
  mkHostProc' (contextScope $ edh'context ets) EdhMethod "push" listPush
    >>= \ !mth -> exitEdh ets exit mth
  where
    listPush :: [EdhValue] -> EdhHostProc
    listPush !args !exit' !ets' = do
      modifyTVar' lv (args ++)
      exitEdh ets' exit' $ EdhList l

listPopProc :: List -> EdhHostProc
listPopProc (List _ !lv) !exit !ets =
  mkHostProc' (contextScope $ edh'context ets) EdhMethod "pop" listPop
    >>= \ !mth -> exitEdh ets exit mth
  where
    listPop :: "def'val" ?: EdhValue -> EdhHostProc
    listPop (defaultArg edhNone -> !def'val) !exit' !ets' =
      readTVar lv >>= \case
        (val : rest) -> writeTVar lv rest >> exitEdh ets' exit' val
        _ -> exitEdh ets' exit' def'val

-- | operator (?<=) - element-of tester
elemProc :: EdhIntrinsicOp
elemProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $ \ !rhVal -> case edhUltimate rhVal of
    EdhArgsPack (ArgsPack !vs _) -> exitEdhTx exit (EdhBool $ lhVal `elem` vs)
    EdhList (List _ !l) -> \ !ets -> do
      ll <- readTVar l
      exitEdh ets exit $ EdhBool $ lhVal `elem` ll
    EdhDict (Dict _ !ds) -> \ !ets ->
      iopdLookup lhVal ds >>= \case
        Nothing -> exitEdh ets exit $ EdhBool False
        Just _ -> exitEdh ets exit $ EdhBool True
    _ -> exitEdhTx exit edhNA

-- | operator (|*) - prefix tester
isPrefixOfProc :: EdhIntrinsicOp
isPrefixOfProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $ \ !rhVal !ets ->
    edhValueStr ets (edhUltimate lhVal) $ \ !lhStr ->
      edhValueStr ets (edhUltimate rhVal) $
        \ !rhStr -> exitEdh ets exit $ EdhBool $ lhStr `T.isPrefixOf` rhStr

-- | operator (*|) - suffix tester
hasSuffixProc :: EdhIntrinsicOp
hasSuffixProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $ \ !rhVal !ets ->
    edhValueStr ets (edhUltimate lhVal) $ \ !lhStr ->
      edhValueStr ets (edhUltimate rhVal) $
        \ !rhStr -> exitEdh ets exit $ EdhBool $ rhStr `T.isSuffixOf` lhStr

-- | operator (:>) - prepender
prpdProc :: EdhIntrinsicOp
prpdProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $ \ !rhVal ->
    let !lhv = edhDeCaseWrap lhVal
     in case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !vs !kwargs) ->
            exitEdhTx exit (EdhArgsPack $ ArgsPack (lhv : vs) kwargs)
          EdhList (List _ !l) -> \ !ets -> do
            modifyTVar' l (lhv :)
            exitEdh ets exit rhVal
          EdhDict (Dict _ !ds) -> \ !ets -> val2DictEntry ets lhv $ \(k, v) -> do
            setDictItem k v ds
            exitEdh ets exit rhVal
          _ -> exitEdhTx exit edhNA

-- | operator (<-) - event publisher
evtPubProc :: EdhIntrinsicOp
evtPubProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhSink !es -> evalExprSrc rhExpr $
      \ !rhVal -> publishEvent es (edhDeCaseWrap rhVal) exit
    _ -> exitEdhTx exit edhNA

-- | operator (>>) - list reverse prepender
lstrvrsPrpdProc :: EdhIntrinsicOp
lstrvrsPrpdProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhList (List _ !ll) -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhArgsPack (ArgsPack !vs !kwargs) -> \ !ets -> do
          lll <- readTVar ll
          exitEdh ets exit $ EdhArgsPack $ ArgsPack (reverse lll ++ vs) kwargs
        EdhList (List _ !l) -> \ !ets -> do
          lll <- readTVar ll
          modifyTVar' l (reverse lll ++)
          exitEdh ets exit rhVal
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (=<) - comprehension maker, appender
--  * list comprehension:
--     [] =< for x from range(10) do x*x
--  * dict comprehension:
--     {} =< for x from range(10) do (x, x*x)
--  * args comprehension:
--     () =< for x from range(10) do x*x
--  * list append
--      [] =< (...) / [...] / {...}
--  * dict append
--      {} =< (...) / [...] / {...}
--  * args append
--      () =< (...) / [...] / {...}
cprhProc :: EdhIntrinsicOp
cprhProc !lhExpr rhExpr@(ExprSrc !rhe _) !exit = case deParen' rhe of
  ForExpr !argsRcvr !iterExpr !doExpr -> evalExprSrc lhExpr $ \ !lhVal !ets ->
    case edhUltimate lhVal of
      EdhList (List _ !l) ->
        edhPrepareForLoop
          ets
          argsRcvr
          iterExpr
          doExpr
          (\ !val -> modifyTVar' l (++ [val]))
          (\ !runLoop -> runEdhTx ets $ runLoop $ \_ -> exitEdhTx exit lhVal)
      EdhDict (Dict _ !d) ->
        edhPrepareForLoop
          ets
          argsRcvr
          iterExpr
          doExpr
          (\ !val -> insertToDict ets val d)
          (\ !runLoop -> runEdhTx ets $ runLoop $ \_ -> exitEdhTx exit lhVal)
      EdhArgsPack (ArgsPack !args !kwargs) -> do
        !posArgs <- newTVar args
        !kwArgs <- iopdFromList $ odToList kwargs
        edhPrepareForLoop
          ets
          argsRcvr
          iterExpr
          doExpr
          ( \ !val -> case val of
              EdhArgsPack (ArgsPack !args' !kwargs') -> do
                modifyTVar' posArgs (++ args')
                iopdUpdate (odToList kwargs') kwArgs
              _ -> modifyTVar' posArgs (++ [val])
          )
          $ \ !runLoop -> runEdhTx ets $
            runLoop $ \_ _ets -> do
              args' <- readTVar posArgs
              kwargs' <- iopdSnapshot kwArgs
              exitEdh ets exit (EdhArgsPack $ ArgsPack args' kwargs')
      _ ->
        throwEdh ets EvalError $
          "don't know how to comprehend into a "
            <> edhTypeNameOf lhVal
            <> ": "
            <> T.pack (show lhVal)
  _ -> evalExprSrc lhExpr $ \ !lhVal -> evalExprSrc rhExpr $ \ !rhVal !ets ->
    case edhUltimate lhVal of
      EdhArgsPack (ArgsPack !vs !kwvs) -> case edhUltimate rhVal of
        EdhArgsPack (ArgsPack !args !kwargs) -> do
          !kwIOPD <- iopdFromList $ odToList kwvs
          iopdUpdate (odToList kwargs) kwIOPD
          kwargs' <- iopdSnapshot kwIOPD
          exitEdh ets exit (EdhArgsPack $ ArgsPack (vs ++ args) kwargs')
        EdhList (List _ !l) -> do
          !ll <- readTVar l
          exitEdh ets exit (EdhArgsPack $ ArgsPack (vs ++ ll) kwvs)
        EdhDict (Dict _ !ds) ->
          dictEntryList ds >>= \ !del ->
            exitEdh ets exit (EdhArgsPack $ ArgsPack (vs ++ del) kwvs)
        _ -> exitEdh ets exit edhNA
      EdhList (List _ !l) -> case edhUltimate rhVal of
        EdhArgsPack (ArgsPack !args _) -> do
          modifyTVar' l (++ args)
          exitEdh ets exit lhVal
        EdhList (List _ !l') -> do
          !ll <- readTVar l'
          modifyTVar' l (++ ll)
          exitEdh ets exit lhVal
        EdhDict (Dict _ !ds) ->
          dictEntryList ds >>= \ !del -> do
            modifyTVar' l (++ del)
            exitEdh ets exit lhVal
        _ -> exitEdh ets exit edhNA
      EdhDict (Dict _ !ds) -> case edhUltimate rhVal of
        EdhArgsPack (ArgsPack _ !kwargs) -> do
          iopdUpdate [(attrKeyValue k, v) | (k, v) <- odToList kwargs] ds
          exitEdh ets exit lhVal
        EdhList (List _ !l) -> do
          !ll <- readTVar l
          pvlToDictEntries ets ll $ \ !del -> do
            iopdUpdate del ds
            exitEdh ets exit lhVal
        EdhDict (Dict _ !ds') -> do
          flip iopdUpdate ds =<< iopdToList ds'
          exitEdh ets exit lhVal
        _ -> exitEdh ets exit edhNA
      _ -> exitEdh ets exit edhNA
  where
    insertToDict :: EdhThreadState -> EdhValue -> DictStore -> STM ()
    insertToDict !s !p !d = val2DictEntry s p $ \(k, v) -> setDictItem k v d
