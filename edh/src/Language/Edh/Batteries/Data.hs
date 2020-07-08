
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

import           Language.Edh.Control
import           Language.Edh.Event
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate
import           Language.Edh.Details.Utils


strEncodeProc :: EdhProcedure
strEncodeProc (ArgsPack [EdhString !str] !kwargs) !exit | Map.null kwargs =
  exitEdhProc exit $ EdhBlob $ TE.encodeUtf8 str
strEncodeProc _ _ =
  throwEdh EvalError "bug: __StringType_bytes__ got unexpected args"

blobDecodeProc :: EdhProcedure
blobDecodeProc (ArgsPack [EdhBlob !blob] !kwargs) !exit | Map.null kwargs =
  exitEdhProc exit $ EdhString $ TE.decodeUtf8 blob
blobDecodeProc _ _ =
  throwEdh EvalError "bug: __BlobType_utf8string__ got unexpected args"


propertyProc :: EdhProcedure
propertyProc !apk !exit =
  case parseArgsPack (Nothing, Nothing) argsParser apk of
    Left !err -> throwEdh UsageError err
    Right (Nothing, _) ->
      throwEdh UsageError "Missing getter method to define a property"
    Right (Just getter, setter) -> ask >>= \ !pgs -> contEdhSTM $ do
      let !ctx  = edh'context pgs
          !this = thisObject $ contextFrame ctx 1
          !pd   = EdhDescriptor getter setter
          !name = procedure'name getter
      when (name /= AttrByName "_")
        $ unless (contextPure ctx)
        $ changeEntityAttr pgs (objEntity this) name pd
      exitEdhSTM pgs exit pd
 where
  argsParser =
    ArgsPackParser
        [ \arg (_, setter) -> case arg of
          EdhMethod !getter -> Right (Just getter, setter)
          !badVal ->
            Left
              $  "Need a method procedure to define a property, not a: "
              <> T.pack (edhTypeNameOf badVal)
        , \arg (getter, _) -> case arg of
          EdhMethod !setter -> Right (getter, Just setter)
          !badVal ->
            Left
              $  "Need a method procedure to define a property, not a: "
              <> T.pack (edhTypeNameOf badVal)
        ]
      $ Map.fromList
          [ ( "getter"
            , \arg (_, setter) -> case arg of
              EdhMethod !getter -> Right (Just getter, setter)
              !badVal ->
                Left
                  $  "Need a method procedure to define a property, not a: "
                  <> T.pack (edhTypeNameOf badVal)
            )
          , ( "setter"
            , \arg (getter, _) -> case arg of
              EdhMethod !setter -> Right (getter, Just setter)
              !badVal ->
                Left
                  $  "Need a method procedure to define a property, not a: "
                  <> T.pack (edhTypeNameOf badVal)
            )
          ]

setterProc :: EdhProcedure
setterProc (ArgsPack [EdhMethod !setter] !kwargs) !exit | Map.null kwargs =
  ask >>= \ !pgs -> contEdhSTM $ do
    let !ctx  = edh'context pgs
        !this = thisObject $ contextFrame ctx 1
        !name = procedure'name setter
    if name == AttrByName "_"
      then throwEdhSTM pgs UsageError "Why you want a setter named `_` ?"
      else lookupEdhObjAttr pgs this name >>= \case
        EdhDescriptor !getter _ -> do
          let !pd = EdhDescriptor getter $ Just setter
          unless (contextPure ctx)
            $ changeEntityAttr pgs (objEntity this) name pd
          exitEdhSTM pgs exit pd
        _ ->
          throwEdhSTM pgs UsageError $ "Missing property getter " <> T.pack
            (show name)
setterProc _ _ = throwEdh EvalError "Invalid args to setter"


-- | operator (@) - attribute key dereferencing
attrDerefAddrProc :: EdhIntrinsicOp
attrDerefAddrProc !lhExpr !rhExpr !exit =
  evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case edhUltimate rhVal of
    EdhExpr _ (AttrExpr (DirectRef !addr)) _ -> ask >>= \pgs ->
      contEdhSTM
        $ resolveEdhAttrAddr pgs addr
        $ \key -> runEdhProc pgs
            $ getEdhAttr lhExpr key (noAttr $ T.pack $ show key) exit
    EdhString !attrName ->
      getEdhAttr lhExpr (AttrByName attrName) (noAttr attrName) exit
    EdhSymbol sym@(Symbol _ desc) ->
      getEdhAttr lhExpr (AttrBySym sym) (noAttr $ "@" <> desc) exit
    _ -> throwEdh EvalError $ "Invalid attribute reference type - " <> T.pack
      (edhTypeNameOf rhVal)
 where
  noAttr key lhVal =
    throwEdh EvalError
      $  "No such attribute "
      <> key
      <> " from a "
      <> T.pack (edhTypeNameOf lhVal)
      <> ": "
      <> T.pack (show lhVal)


-- | operator ($) - function application
--
-- similar to ($) operator in Haskell
-- can be used to apply decorators with nicer syntax
fapProc :: EdhIntrinsicOp
fapProc !lhExpr !rhExpr !exit = ask >>= \ !pgs ->
  contEdhSTM
    $ resolveEdhCallee pgs lhExpr
    $ \(OriginalValue !callee'val _ !callee'that, scopeMod) ->
        edhMakeCall pgs callee'val callee'that argsPkr scopeMod
          $ \mkCall -> runEdhProc pgs (mkCall exit)
 where
  argsPkr :: ArgsPacker
  argsPkr = case rhExpr of
    ArgsPackExpr !pkr -> pkr
    _                 -> [SendPosArg rhExpr]

-- | operator (|) - flipped function application
--
-- similar to UNIX pipe
ffapProc :: EdhIntrinsicOp
ffapProc !lhExpr !rhExpr !exit = ask >>= \ !pgs ->
  contEdhSTM
    $ resolveEdhCallee pgs rhExpr
    $ \(OriginalValue !callee'val _ !callee'that, scopeMod) ->
        edhMakeCall pgs callee'val callee'that argsPkr scopeMod
          $ \mkCall -> runEdhProc pgs (mkCall exit)
 where
  argsPkr :: ArgsPacker
  argsPkr = case lhExpr of
    ArgsPackExpr !pkr -> pkr
    _                 -> [SendPosArg lhExpr]


-- | operator (:=) - named value definition
defProc :: EdhIntrinsicOp
defProc (AttrExpr (DirectRef (NamedAttr !valName))) !rhExpr !exit = do
  pgs <- ask
  evalExpr rhExpr $ \(OriginalValue !rhV _ _) -> contEdhSTM $ do
    let !rhVal   = edhDeCaseClose rhV
        !ctx     = edh'context pgs
        !scope   = contextScope ctx
        this     = thisObject scope
        !nv      = EdhNamedValue valName rhVal
        doAssign = do
          changeEntityAttr pgs (scopeEntity scope) (AttrByName valName) nv
          when (contextExporting ctx && objEntity this == scopeEntity scope)
            $   lookupEntityAttr pgs
                                 (objEntity this)
                                 (AttrByName edhExportsMagicName)
            >>= \case
                  EdhDict (Dict _ !thisExpDS) ->
                    modifyTVar' thisExpDS $ Map.insert (EdhString valName) nv
                  _ -> do
                    d <- createEdhDict $ Map.singleton (EdhString valName) nv
                    changeEntityAttr pgs
                                     (objEntity this)
                                     (AttrByName edhExportsMagicName)
                                     d
    lookupEntityAttr pgs (scopeEntity scope) (AttrByName valName) >>= \case
      EdhNil -> do
        doAssign
        exitEdhSTM pgs exit nv
      oldDef@(EdhNamedValue n v) -> if v /= rhVal
        then runEdhProc pgs $ edhValueRepr rhVal $ \(OriginalValue newR _ _) ->
          edhValueRepr oldDef $ \(OriginalValue oldR _ _) -> case newR of
            EdhString !newRepr -> case oldR of
              EdhString oldRepr ->
                throwEdh EvalError
                  $  "Can not redefine "
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
          exitEdhSTM pgs exit nv
      _ -> do
        doAssign
        exitEdhSTM pgs exit nv
defProc !lhExpr _ _ =
  throwEdh EvalError $ "Invalid value definition: " <> T.pack (show lhExpr)


-- | operator (?:=) - named value definition if missing
defMissingProc :: EdhIntrinsicOp
defMissingProc (AttrExpr (DirectRef (NamedAttr "_"))) _ _ =
  throwEdh UsageError "Not so reasonable: _ ?:= xxx"
defMissingProc (AttrExpr (DirectRef (NamedAttr !valName))) !rhExpr !exit = do
  pgs <- ask
  let !ent   = scopeEntity $ contextScope $ edh'context pgs
      !key   = AttrByName valName
      !pgsTx = pgs { edh'in'tx = True } -- must within a tx
  contEdhSTM $ lookupEntityAttr pgsTx ent key >>= \case
    EdhNil ->
      runEdhProc pgsTx $ evalExpr rhExpr $ \(OriginalValue !rhV _ _) ->
        contEdhSTM $ do
          let !rhVal = edhDeCaseClose rhV
              !nv    = EdhNamedValue valName rhVal
          changeEntityAttr pgsTx ent key nv
          exitEdhSTM pgs exit nv
    !preVal -> exitEdhSTM pgs exit preVal
defMissingProc !lhExpr _ _ =
  throwEdh EvalError $ "Invalid value definition: " <> T.pack (show lhExpr)


-- | operator (:) - pair constructor
pairCtorProc :: EdhIntrinsicOp
pairCtorProc !lhExpr !rhExpr !exit = do
  pgs <- ask
  -- make sure left hand and right hand values are evaluated in same tx
  local (const pgs { edh'in'tx = True })
    $ evalExpr lhExpr
    $ \(OriginalValue !lhVal _ _) ->
        evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> contEdhSTM $ exitEdhSTM
          pgs
          exit
          (EdhPair (edhDeCaseClose lhVal) (edhDeCaseClose rhVal))


-- | operator (?) - attribute tempter, 
-- address an attribute off an object if possible, nil otherwise
attrTemptProc :: EdhIntrinsicOp
attrTemptProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  case rhExpr of
    AttrExpr (DirectRef !addr) ->
      contEdhSTM $ resolveEdhAttrAddr pgs addr $ \key ->
        runEdhProc pgs
          $ getEdhAttr lhExpr key (const $ exitEdhProc exit nil) exit
    _ -> throwEdh EvalError $ "Invalid attribute expression: " <> T.pack
      (show rhExpr)

-- | operator (?@) - attribute dereferencing tempter, 
-- address an attribute off an object if possible, nil otherwise
attrDerefTemptProc :: EdhIntrinsicOp
attrDerefTemptProc !lhExpr !rhExpr !exit =
  evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case edhUltimate rhVal of
    EdhExpr _ (AttrExpr (DirectRef !addr)) _ -> ask >>= \pgs ->
      contEdhSTM $ resolveEdhAttrAddr pgs addr $ \key ->
        runEdhProc pgs
          $ getEdhAttr lhExpr key (const $ exitEdhProc exit nil) exit
    EdhString !attrName -> getEdhAttr lhExpr
                                      (AttrByName attrName)
                                      (const $ exitEdhProc exit nil)
                                      exit
    EdhSymbol !sym ->
      getEdhAttr lhExpr (AttrBySym sym) (const $ exitEdhProc exit nil) exit
    _ -> throwEdh EvalError $ "Invalid attribute reference type - " <> T.pack
      (edhTypeNameOf rhVal)


-- | the Symbol(repr, *reprs) constructor
symbolCtorProc :: EdhProcedure
symbolCtorProc (ArgsPack _ !kwargs) _ | not $ Map.null kwargs =
  throwEdh UsageError "No kwargs should be passed to Symbol()"
symbolCtorProc (ArgsPack !reprs _) !exit = ask >>= \pgs -> contEdhSTM $ do
  let ctorSym :: EdhValue -> (Symbol -> STM ()) -> STM ()
      ctorSym (EdhString !repr) !exit' = mkSymbol repr >>= exit'
      ctorSym _ _ = throwEdhSTM pgs EvalError "Invalid arg to Symbol()"
  seqcontSTM (ctorSym <$> reprs) $ \case
    [sym] -> exitEdhSTM pgs exit $ EdhSymbol sym
    syms ->
      exitEdhSTM pgs exit $ EdhArgsPack $ ArgsPack (EdhSymbol <$> syms) mempty

apkArgsProc :: EdhProcedure
apkArgsProc (ArgsPack _ !kwargs) _ | not $ Map.null kwargs =
  throwEdh EvalError "bug: __ArgsPackType_args__ got kwargs"
apkArgsProc (ArgsPack [EdhArgsPack (ArgsPack !args _)] _) !exit =
  exitEdhProc exit $ EdhArgsPack $ ArgsPack args Map.empty
apkArgsProc _ _ =
  throwEdh EvalError "bug: __ArgsPackType_args__ got unexpected args"

apkKwrgsProc :: EdhProcedure
apkKwrgsProc (ArgsPack _ !kwargs) _ | not $ Map.null kwargs =
  throwEdh EvalError "bug: __ArgsPackType_kwargs__ got kwargs"
apkKwrgsProc (ArgsPack [EdhArgsPack (ArgsPack _ !kwargs')] _) !exit =
  exitEdhProc exit $ EdhArgsPack $ ArgsPack [] kwargs'
apkKwrgsProc _ _ =
  throwEdh EvalError "bug: __ArgsPackType_kwargs__ got unexpected args"


-- | utility repr(*args,**kwargs) - repr extractor
reprProc :: EdhProcedure
reprProc (ArgsPack !args !kwargs) !exit = do
  pgs <- ask
  let go
        :: [EdhValue]
        -> [(AttrKey, EdhValue)]
        -> [EdhValue]
        -> [(AttrKey, EdhValue)]
        -> STM ()
      go [repr] kwReprs [] [] | null kwReprs = exitEdhSTM pgs exit repr
      go reprs kwReprs [] [] =
        exitEdhSTM pgs exit
          $ EdhArgsPack
          $ ArgsPack (reverse reprs)
          $ Map.fromList kwReprs
      go reprs kwReprs (v : rest) kwps =
        runEdhProc pgs $ edhValueRepr v $ \(OriginalValue r _ _) ->
          contEdhSTM $ go (r : reprs) kwReprs rest kwps
      go reprs kwReprs [] ((k, v) : rest) =
        runEdhProc pgs $ edhValueRepr v $ \(OriginalValue r _ _) ->
          contEdhSTM $ go reprs ((k, r) : kwReprs) [] rest
  contEdhSTM $ go [] [] args (Map.toList kwargs)


-- | operator (++) - string coercing concatenator
concatProc :: EdhIntrinsicOp
concatProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhv _ _) -> case edhUltimate lhv of
    EdhBlob !lhBlob -> evalExpr rhExpr $ \(OriginalValue !rhv _ _) ->
      case edhUltimate rhv of
        EdhBlob !rhBlob -> exitEdhProc exit $ EdhBlob $ lhBlob <> rhBlob
        EdhString !rhStr ->
          exitEdhProc exit $ EdhBlob $ lhBlob <> TE.encodeUtf8 rhStr
        rhVal ->
          throwEdh UsageError
            $  "Should not (++) a "
            <> T.pack (edhTypeNameOf rhVal)
            <> " to a blob."
    lhVal -> edhValueStr lhVal $ \(OriginalValue lhStr _ _) -> case lhStr of
      EdhString !lhs -> evalExpr rhExpr $ \(OriginalValue !rhv _ _) ->
        edhValueStr (edhDeCaseClose $ edhUltimate rhv)
          $ \(OriginalValue rhStr _ _) -> case rhStr of
              EdhString !rhs -> exitEdhProc exit (EdhString $ lhs <> rhs)
              _              -> error "bug: edhValueStr returned non-string"
      _ -> error "bug: edhValueStr returned non-string"


-- | utility null(*args,**kwargs) - null tester
isNullProc :: EdhProcedure
isNullProc (ArgsPack !args !kwargs) !exit = do
  !pgs <- ask
  contEdhSTM $ if null kwargs
    then case args of
      [v] ->
        edhValueNull pgs v $ \isNull -> exitEdhSTM pgs exit $ EdhBool isNull
      _ -> seqcontSTM (edhValueNull pgs <$> args) $ \argsNulls ->
        exitEdhSTM pgs exit $ EdhArgsPack $ ArgsPack (EdhBool <$> argsNulls)
                                                     mempty
    else seqcontSTM (edhValueNull pgs <$> args) $ \argsNulls ->
      seqcontSTM
          [ \exit' -> edhValueNull pgs v (\isNull -> exit' (k, isNull))
          | (k, v) <- Map.toList kwargs
          ]
        $ \kwargsNulls -> exitEdhSTM
            pgs
            exit
            (EdhArgsPack $ ArgsPack
              (EdhBool <$> argsNulls)
              (Map.map EdhBool $ Map.fromList kwargsNulls)
            )


-- | utility type(*args,**kwargs) - value type introspector
typeProc :: EdhProcedure
typeProc (ArgsPack !args !kwargs) !exit =
  let !argsType = edhTypeValOf <$> args
  in  if null kwargs
        then case argsType of
          [t] -> exitEdhProc exit t
          _   -> exitEdhProc exit $ EdhArgsPack $ ArgsPack argsType mempty
        else exitEdhProc
          exit
          (EdhArgsPack $ ArgsPack argsType $ Map.map edhTypeValOf kwargs)
 where
  edhTypeValOf :: EdhValue -> EdhValue
  edhTypeValOf EdhNil              = EdhNil
  edhTypeValOf (EdhNamedValue n v) = EdhNamedValue n $ edhTypeValOf v
  edhTypeValOf v                   = EdhType $ edhTypeOf v


procNameProc :: EdhProcedure
procNameProc (ArgsPack _ !kwargs) _ | not $ Map.null kwargs =
  throwEdh EvalError "bug: __ProcType_name__ got kwargs"
procNameProc (ArgsPack [EdhIntrOp _ (IntrinOpDefi _ !opSym _)] _) !exit =
  exitEdhProc exit $ EdhString $ "(" <> opSym <> ")"
procNameProc (ArgsPack [EdhClass !pd] _) !exit =
  exitEdhProc exit $ EdhString $ procedureName pd
procNameProc (ArgsPack [EdhMethod !pd] _) !exit =
  exitEdhProc exit $ EdhString $ procedureName pd
procNameProc (ArgsPack [EdhOprtor _ _ !pd] _) !exit =
  exitEdhProc exit $ EdhString $ procedureName pd
procNameProc (ArgsPack [EdhGnrtor !pd] _) !exit =
  exitEdhProc exit $ EdhString $ procedureName pd
procNameProc (ArgsPack [EdhIntrpr !pd] _) !exit =
  exitEdhProc exit $ EdhString $ procedureName pd
procNameProc (ArgsPack [EdhPrducr !pd] _) !exit =
  exitEdhProc exit $ EdhString $ procedureName pd
procNameProc _ _ =
  throwEdh EvalError "bug: __ProcType_name__ got unexpected args"


-- | utility dict(***apk,**kwargs,*args) - dict constructor by arguments
-- can be used to convert arguments pack into dict
dictProc :: EdhProcedure
dictProc (ArgsPack !args !kwargs) !exit = do
  !pgs <- ask
  contEdhSTM $ do
    let !kwDict = Map.fromList $ (<$> Map.toList kwargs) $ \(key, val) ->
          (attrKeyValue key, val)
    u <- unsafeIOToSTM newUnique
    d <- newTVar $ Map.union kwDict $ Map.fromList
      [ (EdhDecimal (fromIntegral i), t) | (i, t) <- zip [(0 :: Int) ..] args ]
    exitEdhSTM pgs exit (EdhDict (Dict u d))

dictSizeProc :: EdhProcedure
dictSizeProc (ArgsPack _ !kwargs) _ | not $ Map.null kwargs =
  throwEdh EvalError "bug: __DictType_size__ got kwargs"
dictSizeProc (ArgsPack [EdhDict (Dict _ !dsv)] _) !exit = do
  !pgs <- ask
  contEdhSTM $ do
    ds <- readTVar dsv
    exitEdhSTM pgs exit $ EdhDecimal $ fromIntegral $ Map.size ds
dictSizeProc _ _ =
  throwEdh EvalError "bug: __DictType_size__ got unexpected args"


listPushProc :: EdhProcedure
listPushProc (ArgsPack _ !kwargs) _ | not $ Map.null kwargs =
  throwEdh EvalError "bug: __ListType_push__ got kwargs"
listPushProc (ArgsPack [l@(EdhList (List _ !lv))] _) !exit = do
  !pgs <- ask
  contEdhSTM
    $   mkHostProc (contextScope $ edh'context pgs)
                   EdhMethod
                   "push"
                   listPush
                   (PackReceiver [RecvRestPosArgs "values"])
    >>= \mth -> exitEdhSTM pgs exit mth
 where
  listPush :: EdhProcedure
  listPush (ArgsPack !args !kwargs') !exit' | Map.null kwargs' =
    ask >>= \pgs -> contEdhSTM $ do
      modifyTVar' lv (args ++)
      exitEdhSTM pgs exit' l
  listPush _ _ = throwEdh UsageError "Invalid args to list.push()"
listPushProc _ _ =
  throwEdh EvalError "bug: __ListType_push__ got unexpected args"

listPopProc :: EdhProcedure
listPopProc (ArgsPack _ !kwargs) _ | not $ Map.null kwargs =
  throwEdh EvalError "bug: __ListType_pop__ got kwargs"
listPopProc (ArgsPack [EdhList (List _ !lv)] _) !exit = do
  !pgs <- ask
  contEdhSTM
    $   mkHostProc (contextScope $ edh'context pgs)
                   EdhMethod
                   "pop"
                   listPop
                   (PackReceiver [optionalArg "default" $ IntplSubs edhNone])
    >>= \mth -> exitEdhSTM pgs exit mth
 where
  listPop :: EdhProcedure
  listPop !apk !exit' = case parseArgsPack edhNone parseArgs apk of
    Left  err     -> throwEdh UsageError err
    Right !defVal -> ask >>= \pgs -> contEdhSTM $ readTVar lv >>= \case
      (val : rest) -> writeTVar lv rest >> exitEdhSTM pgs exit' val
      _            -> exitEdhSTM pgs exit' defVal
   where
    parseArgs = ArgsPackParser [\arg _ -> Right arg]
      $ Map.fromList [("default", \arg _ -> Right arg)]
listPopProc _ _ =
  throwEdh EvalError "bug: __ListType_pop__ got unexpected args"


-- | operator (?<=) - element-of tester
elemProc :: EdhIntrinsicOp
elemProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case edhUltimate rhVal of
      EdhArgsPack (ArgsPack !vs _) ->
        exitEdhProc exit (EdhBool $ lhVal `elem` vs)
      EdhList (List _ !l) -> contEdhSTM $ do
        ll <- readTVar l
        exitEdhSTM pgs exit $ EdhBool $ lhVal `elem` ll
      EdhDict (Dict _ !d) -> contEdhSTM $ do
        ds <- readTVar d
        exitEdhSTM pgs exit $ EdhBool $ case Map.lookup lhVal ds of
          Nothing -> False
          Just _  -> True
      _ -> exitEdhProc exit EdhContinue


-- | operator (|*) - prefix tester
isPrefixOfProc :: EdhIntrinsicOp
isPrefixOfProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    edhValueStr (edhUltimate lhVal) $ \(OriginalValue lhRepr _ _) ->
      case lhRepr of
        EdhString !lhStr -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
          edhValueStr (edhUltimate rhVal) $ \(OriginalValue !rhRepr _ _) ->
            case rhRepr of
              EdhString !rhStr ->
                exitEdhProc exit $ EdhBool $ lhStr `T.isPrefixOf` rhStr
              _ -> error "bug: edhValueStr returned non-string"
        _ -> error "bug: edhValueStr returned non-string"

-- | operator (*|) - suffix tester
hasSuffixProc :: EdhIntrinsicOp
hasSuffixProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    edhValueStr (edhUltimate lhVal) $ \(OriginalValue lhRepr _ _) ->
      case lhRepr of
        EdhString !lhStr -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
          edhValueStr (edhUltimate rhVal) $ \(OriginalValue !rhRepr _ _) ->
            case rhRepr of
              EdhString !rhStr ->
                exitEdhProc exit $ EdhBool $ rhStr `T.isSuffixOf` lhStr
              _ -> error "bug: edhValueStr returned non-string"
        _ -> error "bug: edhValueStr returned non-string"


-- | operator (=>) - prepender
prpdProc :: EdhIntrinsicOp
prpdProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhV _ _) ->
    let !lhVal = edhDeCaseClose lhV
    in
      evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case edhUltimate rhVal of
        EdhArgsPack (ArgsPack !vs !kwargs) ->
          exitEdhProc exit (EdhArgsPack $ ArgsPack (lhVal : vs) kwargs)
        EdhList (List _ !l) -> contEdhSTM $ do
          modifyTVar' l (lhVal :)
          exitEdhSTM pgs exit rhVal
        EdhDict (Dict _ !d) ->
          contEdhSTM $ val2DictEntry pgs lhVal $ \(k, v) -> do
            modifyTVar' d (setDictItem k v)
            exitEdhSTM pgs exit rhVal
        _ -> exitEdhProc exit EdhContinue


-- | operator (>>) - list reverse prepender
lstrvrsPrpdProc :: EdhIntrinsicOp
lstrvrsPrpdProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhList (List _ !ll) -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhArgsPack (ArgsPack !vs !kwargs) -> contEdhSTM $ do
          lll <- readTVar ll
          exitEdhSTM pgs exit $ EdhArgsPack $ ArgsPack (reverse lll ++ vs)
                                                       kwargs
        EdhList (List _ !l) -> contEdhSTM $ do
          lll <- readTVar ll
          modifyTVar' l (reverse lll ++)
          exitEdhSTM pgs exit rhVal
        _ -> exitEdhProc exit EdhContinue
    _ -> exitEdhProc exit EdhContinue


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
  !pgs <- ask
  let insertToDict :: EdhValue -> TVar DictStore -> STM ()
      insertToDict p d =
        val2DictEntry pgs p $ \(k, v) -> modifyTVar' d $ setDictItem k v
  case rhExpr of
    ForExpr argsRcvr iterExpr doExpr ->
      evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
        EdhList (List _ !l) -> contEdhSTM $ edhForLoop
          pgs
          argsRcvr
          iterExpr
          doExpr
          (\val -> modifyTVar' l (++ [val]))
          (\mkLoop -> runEdhProc pgs $ mkLoop $ \_ -> exitEdhProc exit lhVal)
        EdhDict (Dict _ !d) -> contEdhSTM $ edhForLoop
          pgs
          argsRcvr
          iterExpr
          doExpr
          (\val -> insertToDict val d)
          (\mkLoop -> runEdhProc pgs $ mkLoop $ \_ -> exitEdhProc exit lhVal)
        EdhArgsPack !apk -> contEdhSTM $ do
          apkVar <- newTVar apk
          edhForLoop
              pgs
              argsRcvr
              iterExpr
              doExpr
              (\val -> modifyTVar' apkVar $ \(ArgsPack !args !kwargs) ->
                case val of
                  EdhArgsPack (ArgsPack !args' !kwargs') ->
                    ArgsPack (args ++ args') (Map.union kwargs' kwargs)
                  _ -> ArgsPack (args ++ [val]) kwargs
              )
            $ \mkLoop -> runEdhProc pgs $ mkLoop $ \_ -> contEdhSTM $ do
                apk' <- readTVar apkVar
                exitEdhSTM pgs exit (EdhArgsPack apk')
        _ ->
          throwEdh EvalError
            $  "Don't know how to comprehend into a "
            <> T.pack (edhTypeNameOf lhVal)
            <> ": "
            <> T.pack (show lhVal)
    _ -> evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
      evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case edhUltimate lhVal of
        EdhArgsPack (ArgsPack !vs kwargs) -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !args _) ->
            exitEdhProc exit (EdhArgsPack $ ArgsPack (vs ++ args) kwargs)
          EdhList (List _ !l) -> contEdhSTM $ do
            ll <- readTVar l
            exitEdhSTM pgs exit (EdhArgsPack $ ArgsPack (vs ++ ll) kwargs)
          EdhDict (Dict _ !d) -> contEdhSTM $ do
            ds <- readTVar d
            exitEdhSTM
              pgs
              exit
              (EdhArgsPack $ ArgsPack (vs ++ dictEntryList ds) kwargs)
          _ -> exitEdhProc exit EdhContinue
        EdhList (List _ !l) -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !args _) -> contEdhSTM $ do
            modifyTVar' l (++ args)
            exitEdhSTM pgs exit lhVal
          EdhList (List _ !l') -> contEdhSTM $ do
            ll <- readTVar l'
            modifyTVar' l (++ ll)
            exitEdhSTM pgs exit lhVal
          EdhDict (Dict _ !d) -> contEdhSTM $ do
            ds <- readTVar d
            modifyTVar' l (++ (dictEntryList ds))
            exitEdhSTM pgs exit lhVal
          _ -> exitEdhProc exit EdhContinue
        EdhDict (Dict _ !d) -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack _ !kwargs) -> contEdhSTM $ do
            modifyTVar d $ Map.union $ Map.fromList
              [ (attrKeyValue k, v) | (k, v) <- Map.toList kwargs ]
            exitEdhSTM pgs exit lhVal
          EdhList (List _ !l) -> contEdhSTM $ do
            ll <- readTVar l
            pvlToDict pgs ll $ \d' -> do
              modifyTVar d $ Map.union d'
              exitEdhSTM pgs exit lhVal
          EdhDict (Dict _ !d') -> contEdhSTM $ do
            ds <- readTVar d'
            modifyTVar d $ Map.union ds
            exitEdhSTM pgs exit lhVal
          _ -> exitEdhProc exit EdhContinue
        _ -> exitEdhProc exit EdhContinue


-- | operator (<-) - event publisher
evtPubProc :: EdhIntrinsicOp
evtPubProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhSink !es -> evalExpr rhExpr $ \(OriginalValue !rhV _ _) ->
      let !rhVal = edhDeCaseClose rhV
      in  contEdhSTM $ do
            publishEvent es rhVal
            exitEdhSTM pgs exit rhVal
    _ -> exitEdhProc exit EdhContinue

