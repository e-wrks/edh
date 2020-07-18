
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
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate
import           Language.Edh.Details.Utils


strEncodeProc :: EdhProcedure
strEncodeProc (ArgsPack [EdhString !str] !kwargs) !exit | odNull kwargs =
  exitEdhProc exit $ EdhBlob $ TE.encodeUtf8 str
strEncodeProc _ _ =
  throwEdh EvalError "bug: __StringType_bytes__ got unexpected args"

blobDecodeProc :: EdhProcedure
blobDecodeProc (ArgsPack [EdhBlob !blob] !kwargs) !exit | odNull kwargs =
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
setterProc (ArgsPack [EdhMethod !setter] !kwargs) !exit | odNull kwargs =
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
                    iopdInsert (EdhString valName) nv thisExpDS
                  _ -> do
                    d <- createEdhDict [(EdhString valName, nv)]
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
symbolCtorProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
  throwEdh UsageError "No kwargs should be passed to Symbol()"
symbolCtorProc (ArgsPack !reprs _) !exit = ask >>= \pgs -> contEdhSTM $ do
  let ctorSym :: EdhValue -> (Symbol -> STM ()) -> STM ()
      ctorSym (EdhString !repr) !exit' = mkSymbol repr >>= exit'
      ctorSym _ _ = throwEdhSTM pgs EvalError "Invalid arg to Symbol()"
  seqcontSTM (ctorSym <$> reprs) $ \case
    [sym] -> exitEdhSTM pgs exit $ EdhSymbol sym
    syms ->
      exitEdhSTM pgs exit $ EdhArgsPack $ ArgsPack (EdhSymbol <$> syms) odEmpty

apkArgsProc :: EdhProcedure
apkArgsProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
  throwEdh EvalError "bug: __ArgsPackType_args__ got kwargs"
apkArgsProc (ArgsPack [EdhArgsPack (ArgsPack !args _)] _) !exit =
  exitEdhProc exit $ EdhArgsPack $ ArgsPack args odEmpty
apkArgsProc _ _ =
  throwEdh EvalError "bug: __ArgsPackType_args__ got unexpected args"

apkKwrgsProc :: EdhProcedure
apkKwrgsProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
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
          $ odFromList kwReprs
      go reprs kwReprs (v : rest) kwps =
        runEdhProc pgs $ edhValueRepr v $ \(OriginalValue r _ _) ->
          contEdhSTM $ go (r : reprs) kwReprs rest kwps
      go reprs kwReprs [] ((k, v) : rest) =
        runEdhProc pgs $ edhValueRepr v $ \(OriginalValue r _ _) ->
          contEdhSTM $ go reprs ((k, r) : kwReprs) [] rest
  contEdhSTM $ go [] [] args (odToList kwargs)

showProc :: EdhProcedure
showProc (ArgsPack [v] _) !exit = do
  !pgs <- ask
  let -- todo specialize more informative show for intrinsic types of values
    showWithNoMagic = edhValueReprSTM pgs v $ \ !r ->
      exitEdhSTM pgs exit $ EdhString $ T.pack (edhTypeNameOf v) <> ": " <> r
  contEdhSTM $ case v of
    EdhObject !o -> lookupEdhObjAttr pgs o (AttrByName "__show__") >>= \case
      EdhNil -> showWithNoMagic
      EdhMethod !mth ->
        runEdhProc pgs $ callEdhMethod o mth (ArgsPack [] odEmpty) id exit
      !badMagic ->
        throwEdhSTM pgs UsageError
          $  "Bad magic __show__ of "
          <> T.pack (edhTypeNameOf badMagic)
          <> " on class "
          <> procedureName (objClass o)
    _ -> showWithNoMagic
showProc _ _ = throwEdh UsageError "Please show one value at a time"

descProc :: EdhProcedure
descProc (ArgsPack [v] _) !exit = do
  !pgs <- ask
  let -- TODO specialize more informative description (statistical wise) for
      --      intrinsic types of values
      descWithNoMagic = edhValueReprSTM pgs v $ \ !r -> case v of
        EdhObject !o ->
          exitEdhSTM pgs exit
            $  EdhString
            $  "It is an object of class "
            <> procedureName (objClass o)
            <> ", having representation:\n"
            <> r
        _ ->
          exitEdhSTM pgs exit
            $  EdhString
            $  "It is of "
            <> T.pack (edhTypeNameOf v)
            <> ", having representation:\n"
            <> r
  contEdhSTM $ case v of
    EdhObject !o -> lookupEdhObjAttr pgs o (AttrByName "__desc__") >>= \case
      EdhNil -> descWithNoMagic
      EdhMethod !mth ->
        runEdhProc pgs $ callEdhMethod o mth (ArgsPack [] odEmpty) id exit
      !badMagic ->
        throwEdhSTM pgs UsageError
          $  "Bad magic __desc__ of "
          <> T.pack (edhTypeNameOf badMagic)
          <> " on class "
          <> procedureName (objClass o)
    _ -> descWithNoMagic
descProc _ _ = throwEdh UsageError "Please describe one value at a time"


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
  contEdhSTM $ if odNull kwargs
    then case args of
      [v] ->
        edhValueNull pgs v $ \isNull -> exitEdhSTM pgs exit $ EdhBool isNull
      _ -> seqcontSTM (edhValueNull pgs <$> args) $ \ !argsNulls ->
        exitEdhSTM pgs exit $ EdhArgsPack $ ArgsPack (EdhBool <$> argsNulls)
                                                     odEmpty
    else seqcontSTM (edhValueNull pgs <$> args) $ \argsNulls ->
      seqcontSTM
          [ \exit' ->
              edhValueNull pgs v (\ !isNull -> exit' (k, EdhBool isNull))
          | (k, v) <- odToList kwargs
          ]
        $ \ !kwargsNulls -> exitEdhSTM
            pgs
            exit
            ( EdhArgsPack
            $ ArgsPack (EdhBool <$> argsNulls) (odFromList kwargsNulls)
            )


-- | utility type(*args,**kwargs) - value type introspector
typeProc :: EdhProcedure
typeProc (ArgsPack !args !kwargs) !exit =
  let !argsType = edhTypeValOf <$> args
  in  if odNull kwargs
        then case argsType of
          [t] -> exitEdhProc exit t
          _   -> exitEdhProc exit $ EdhArgsPack $ ArgsPack argsType odEmpty
        else exitEdhProc
          exit
          (EdhArgsPack $ ArgsPack argsType $ odMap edhTypeValOf kwargs)
 where
  edhTypeValOf :: EdhValue -> EdhValue
  edhTypeValOf EdhNil              = EdhNil
  edhTypeValOf (EdhNamedValue n v) = EdhNamedValue n $ edhTypeValOf v
  edhTypeValOf v                   = EdhType $ edhTypeOf v


procNameProc :: EdhProcedure
procNameProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
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
    !ds <-
      iopdFromList
        $ [ (EdhDecimal (fromIntegral i), t)
          | (i, t) <- zip [(0 :: Int) ..] args
          ]
    flip iopdUpdate ds $ (<$> odToList kwargs) $ \(key, val) ->
      (attrKeyValue key, val)
    u <- unsafeIOToSTM newUnique
    exitEdhSTM pgs exit (EdhDict (Dict u ds))

dictSizeProc :: EdhProcedure
dictSizeProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
  throwEdh EvalError "bug: __DictType_size__ got kwargs"
dictSizeProc (ArgsPack [EdhDict (Dict _ !ds)] _) !exit = do
  !pgs <- ask
  contEdhSTM $ exitEdhSTM pgs exit . EdhDecimal . fromIntegral =<< iopdSize ds
dictSizeProc _ _ =
  throwEdh EvalError "bug: __DictType_size__ got unexpected args"


listPushProc :: EdhProcedure
listPushProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
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
  listPush (ArgsPack !args !kwargs') !exit' | odNull kwargs' = ask >>= \pgs ->
    contEdhSTM $ do
      modifyTVar' lv (args ++)
      exitEdhSTM pgs exit' l
  listPush _ _ = throwEdh UsageError "Invalid args to list.push()"
listPushProc _ _ =
  throwEdh EvalError "bug: __ListType_push__ got unexpected args"

listPopProc :: EdhProcedure
listPopProc (ArgsPack _ !kwargs) _ | not $ odNull kwargs =
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
      EdhDict (Dict _ !ds) -> contEdhSTM $ iopdLookup lhVal ds >>= \case
        Nothing -> exitEdhSTM pgs exit $ EdhBool False
        Just _  -> exitEdhSTM pgs exit $ EdhBool True
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
        EdhDict (Dict _ !ds) ->
          contEdhSTM $ val2DictEntry pgs lhVal $ \(k, v) -> do
            setDictItem k v ds
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
  let insertToDict :: EdhValue -> DictStore -> STM ()
      insertToDict !p !d = val2DictEntry pgs p $ \(k, v) -> setDictItem k v d
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
        EdhArgsPack (ArgsPack !args !kwargs) -> contEdhSTM $ do
          !posArgs <- newTVar args
          !kwArgs  <- iopdFromList $ odToList kwargs
          edhForLoop
              pgs
              argsRcvr
              iterExpr
              doExpr
              (\val -> case val of
                EdhArgsPack (ArgsPack !args' !kwargs') -> do
                  modifyTVar' posArgs (++ args')
                  iopdUpdate (odToList kwargs') kwArgs
                _ -> modifyTVar' posArgs (++ [val])
              )
            $ \mkLoop -> runEdhProc pgs $ mkLoop $ \_ -> contEdhSTM $ do
                args'   <- readTVar posArgs
                kwargs' <- iopdSnapshot kwArgs
                exitEdhSTM pgs exit (EdhArgsPack $ ArgsPack args' kwargs')
        _ ->
          throwEdh EvalError
            $  "Don't know how to comprehend into a "
            <> T.pack (edhTypeNameOf lhVal)
            <> ": "
            <> T.pack (show lhVal)
    _ -> evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
      evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case edhUltimate lhVal of
        EdhArgsPack (ArgsPack !vs !kwvs) -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !args !kwargs) -> contEdhSTM $ do
            kwIOPD <- iopdFromList $ odToList kwvs
            iopdUpdate (odToList kwargs) kwIOPD
            kwargs' <- iopdSnapshot kwIOPD
            exitEdhSTM pgs exit (EdhArgsPack $ ArgsPack (vs ++ args) kwargs')
          EdhList (List _ !l) -> contEdhSTM $ do
            ll <- readTVar l
            exitEdhSTM pgs exit (EdhArgsPack $ ArgsPack (vs ++ ll) kwvs)
          EdhDict (Dict _ !ds) ->
            contEdhSTM $ dictEntryList ds >>= \ !del ->
              exitEdhSTM pgs exit (EdhArgsPack $ ArgsPack (vs ++ del) kwvs)
          _ -> exitEdhProc exit EdhContinue
        EdhList (List _ !l) -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !args _) -> contEdhSTM $ do
            modifyTVar' l (++ args)
            exitEdhSTM pgs exit lhVal
          EdhList (List _ !l') -> contEdhSTM $ do
            ll <- readTVar l'
            modifyTVar' l (++ ll)
            exitEdhSTM pgs exit lhVal
          EdhDict (Dict _ !ds) -> contEdhSTM $ dictEntryList ds >>= \ !del ->
            do
              modifyTVar' l (++ del)
              exitEdhSTM pgs exit lhVal
          _ -> exitEdhProc exit EdhContinue
        EdhDict (Dict _ !ds) -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack _ !kwargs) -> contEdhSTM $ do
            iopdUpdate [ (attrKeyValue k, v) | (k, v) <- odToList kwargs ] ds
            exitEdhSTM pgs exit lhVal
          EdhList (List _ !l) -> contEdhSTM $ do
            ll <- readTVar l
            pvlToDictEntries pgs ll $ \ !del -> do
              iopdUpdate del ds
              exitEdhSTM pgs exit lhVal
          EdhDict (Dict _ !ds') -> contEdhSTM $ do
            flip iopdUpdate ds =<< iopdToList ds'
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

