module Language.Edh.Batteries.Data where

-- import           Debug.Trace

import Control.Applicative
import Control.Concurrent.STM
import Control.Monad
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import Data.Char
import Data.Function
import Data.Lossless.Decimal as D (Decimal, nan)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.UUID as UUID
import Data.Unique
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Args
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.InterOp
import Language.Edh.RtTypes
import Prelude

strStripProc :: Text -> EdhHostProc
strStripProc !str !exit = exitEdhTx exit $ EdhString $ T.strip str

strStripStartProc :: Text -> EdhHostProc
strStripStartProc !str !exit = exitEdhTx exit $ EdhString $ T.stripStart str

strStripEndProc :: Text -> EdhHostProc
strStripEndProc !str !exit = exitEdhTx exit $ EdhString $ T.stripEnd str

strEncodeProc :: Text -> EdhHostProc
strEncodeProc !str !exit = exitEdhTx exit $ EdhBlob $ TE.encodeUtf8 str

exprDeBlock :: EdhValue -> EdhHostProc
exprDeBlock (EdhExpr _u _loc _x !src) !exit =
  exitEdhTx exit $ EdhString $ deBlk $ T.lines src
  where
    deBlk :: [Text] -> Text
    deBlk [] = ""
    deBlk (line1 : rest) = case T.stripPrefix "{" content of
      Nothing -> dedent Just indent rest [content]
      Just !content' -> do
        let !content'' = T.strip content'
        case rest of
          [] -> maybe content'' T.stripEnd $ T.stripSuffix "}" content''
          (line2 : rest') -> do
            let (indent2, content2) = T.span isSpace line2
            dedent stripRightBrace indent2 rest' $
              T.stripEnd content2 : [content'' | not $ T.null content'']
      where
        (indent, content) = T.span isSpace line1
    stripRightBrace :: Text -> Maybe Text
    stripRightBrace line = case T.stripSuffix "}" content of
      Nothing -> if T.null content then Nothing else Just content
      Just !content' ->
        let !content'' = T.stripEnd content'
         in if T.null content'' then Nothing else Just content''
      where
        content = T.stripEnd line
    dedent :: (Text -> Maybe Text) -> Text -> [Text] -> [Text] -> Text
    dedent modLastLine !indent !tailLines !headLines = go tailLines headLines
      where
        go [] (lastLine : prevLines) = T.unlines $
          reverse $ case modLastLine lastLine of
            Nothing -> prevLines
            Just !line -> line : prevLines
        go (line : rest) cumLines =
          go rest $
            (: cumLines) $
              maybe (T.stripEnd line) T.stripEnd $ T.stripPrefix indent line
        go [] [] = error "bug: impossible case"
exprDeBlock !v !exit = edhSimpleDescTx v $ \badDesc ->
  exitEdhTx exit $ EdhString $ "not an expr: " <> badDesc

blobDecodeProc :: ByteString -> EdhHostProc
blobDecodeProc !blob !exit = exitEdhTx exit $ EdhString $ TE.decodeUtf8 blob

blobProc :: "val" ?: EdhValue -> RestKwArgs -> EdhHostProc
blobProc (NamedEdhArg Nothing) _ !exit !ets = exitEdh ets exit $ EdhBlob ""
blobProc (NamedEdhArg (Just !val)) !kwargs !exit !ets =
  edhValueBlob' ets val naExit $ exitEdh ets exit . EdhBlob
  where
    naExit = case odLookup (AttrByName "orElse") kwargs of
      Just !altVal -> exitEdh ets exit altVal
      Nothing -> edhSimpleDesc ets val $ \ !badDesc ->
        throwEdh ets UsageError $ "not convertible to blob: " <> badDesc

rngLowerProc :: EdhValue -> EdhHostProc
rngLowerProc (EdhRange !lb _ub) !exit = exitEdhTx exit $ edhBoundValue lb
rngLowerProc _val _exit = throwEdhTx EvalError "not a range"

rngUpperProc :: EdhValue -> EdhHostProc
rngUpperProc (EdhRange _lb !ub) !exit = exitEdhTx exit $ edhBoundValue ub
rngUpperProc _val _exit = throwEdhTx EvalError "not a range"

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
      !badSetter -> edhSimpleDesc ets badSetter $
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
    noAttr !keyRepr !lhVal !ets = edhSimpleDesc ets lhVal $ \ !badDesc ->
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

-- | operator ($@) - out-laid argument sugar, callee at left
--
-- can be used to specify a complex rhs expr (e.g. adhoc arrow procedure) as one
-- more positional argument, or an apk to be merged with lhs call args, at rhs
-- of a procedure call expression.
--
-- this operator can be chained to specified multiple such more arguments.
-- the purpose is better layout.
leftPosCallProc :: EdhIntrinsicOp
leftPosCallProc !lhExpr !rhExpr !exit = do
  let (calleeExpr, apkr) = collapse lhExpr
      synthCall = CallExpr calleeExpr $ merge apkr rhExpr
  evalExpr synthCall exit
  where
    collapse :: ExprSrc -> (ExprSrc, ArgsPacker)
    collapse (ExprSrc (CallExpr calleeExpr apkr) _) = (calleeExpr, apkr)
    collapse (ExprSrc (InfixExpr (OpSymSrc "$@" _) lhx rhx) _) =
      let (calleeExpr, apkr) = collapse lhx
       in (calleeExpr, merge apkr rhx)
    collapse x@(ExprSrc _ aspan) =
      (x, ArgsPacker [] (SrcRange (src'end aspan) (src'end aspan)))

    merge :: ArgsPacker -> ExprSrc -> ArgsPacker
    merge
      (ArgsPacker asndrs aspan)
      (ExprSrc (ArgsPackExpr (ArgsPacker asndrs' aspan')) _) =
        ArgsPacker
          (asndrs ++ asndrs')
          (SrcRange (src'start aspan) (src'end aspan'))
    merge (ArgsPacker asndrs aspan) x@(ExprSrc _ xspan) =
      ArgsPacker
        (asndrs ++ [SendPosArg x])
        (SrcRange (src'start aspan) (src'end xspan))

-- | operator (@|) - out-laid argument sugar, callee at right
--
-- can be used to specify a complex lhs expr (e.g. adhoc arrow procedure) as one
-- more positional argument, or an apk to be merged with rhs call args, at lhs
-- of a procedure call expression.
--
-- this operator can be chained to specified multiple such more arguments.
-- the purpose is better layout.
rightPosCallProc :: EdhIntrinsicOp
rightPosCallProc !lhExpr !rhExpr !exit = do
  let (calleeExpr, apkr) = collapse rhExpr
      synthCall = CallExpr calleeExpr $ merge apkr lhExpr
  evalExpr synthCall exit
  where
    collapse :: ExprSrc -> (ExprSrc, ArgsPacker)
    collapse (ExprSrc (CallExpr calleeExpr apkr) _) = (calleeExpr, apkr)
    collapse (ExprSrc (InfixExpr (OpSymSrc "@|" _) lhx rhx) _) =
      let (calleeExpr, apkr) = collapse rhx
       in (calleeExpr, merge apkr lhx)
    collapse x@(ExprSrc _ aspan) =
      (x, ArgsPacker [] (SrcRange (src'end aspan) (src'end aspan)))

    merge :: ArgsPacker -> ExprSrc -> ArgsPacker
    merge
      (ArgsPacker asndrs aspan)
      (ExprSrc (ArgsPackExpr (ArgsPacker asndrs' aspan')) _) =
        ArgsPacker
          (asndrs' ++ asndrs)
          (SrcRange (src'start aspan') (src'end aspan))
    merge (ArgsPacker asndrs aspan) x@(ExprSrc _ xspan) =
      ArgsPacker
        (SendPosArg x : asndrs)
        (SrcRange (src'start xspan) (src'end aspan))

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
    !calleeVal -> edhMakeCall calleeVal argsPkr exit
  where
    argsPkr :: [ArgSender]
    argsPkr = case rhe of
      ArgsPackExpr (ArgsPacker !pkr _) -> pkr
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
        !rhv = edhDeCaseClose rhVal
        !nv = EdhNamedValue valName rhv
        doDefine = defineScopeAttr ets key nv
    iopdLookup key es >>= \case
      Nothing -> do
        doDefine
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
            unless (n == valName) doDefine
            exitEdh ets exit nv
      _ -> do
        doDefine
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
        let !rhv = edhDeCaseClose rhVal
            !nv = EdhNamedValue valName rhv
        defineScopeAttr ets key nv
        exitEdh ets exit nv
    Just !preVal -> exitEdh ets exit preVal
  where
    !es = edh'scope'entity $ contextScope $ edh'context ets
    !key = AttrByName valName
defMissingProc !lhExpr _ _ !ets =
  throwEdh ets EvalError $ "invalid value definition: " <> T.pack (show lhExpr)

-- | operator (..) (^..) (..^) (^..^) - range constructor
rangeCtorProc ::
  (EdhValue -> EdhBound) -> (EdhValue -> EdhBound) -> EdhIntrinsicOp
rangeCtorProc !lhBndCtor !rhBndCtor !lhExpr !rhExpr !exit =
  evalExprSrc lhExpr $ \ !lhVal -> evalExprSrc rhExpr $ \ !rhVal ->
    exitEdhTx
      exit
      $ EdhRange
        (lhBndCtor $ edhDeCaseWrap lhVal)
        (rhBndCtor $ edhDeCaseWrap rhVal)

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

-- | utility id(val) -- obtain identity value of a value
--
-- this is useful e.g. in log records you have no other way to write
-- information about an event sink, so that it can be evident whether the sink
-- is the same as appeared in another log record. as `repr` of an event sink
-- is always '<sink>'. though it's not a problem when you have those values
-- pertaining to an interactive repl session, where `is` operator can easily
-- tell you that.
idProc :: EdhValue -> EdhHostProc
idProc !val !exit !ets = edhValueIdent val >>= exitEdh ets exit

-- | utility json() - convert the args to json string
jsonProc :: ArgsPack -> EdhHostProc
jsonProc (ArgsPack [value] !kwargs) !exit !ets
  | odNull kwargs =
    edhValueJson ets value $ exitEdh ets exit . EdhString
jsonProc !apk !exit !ets =
  edhValueJson ets (EdhArgsPack apk) $ exitEdh ets exit . EdhString

intrinsicOpReturnNA ::
  EdhTxExit EdhValue ->
  EdhValue ->
  EdhValue ->
  EdhTx
intrinsicOpReturnNA !exit !lhVal !rhVal !ets =
  exitEdh ets exit
    =<< mkDefault''
      Nothing
      (ArgsPack [lhVal, rhVal] odEmpty)
      (LitExpr NilLiteral)

intrinsicOpReturnNA'WithLHV ::
  EdhTxExit EdhValue ->
  EdhValue ->
  EdhTx
intrinsicOpReturnNA'WithLHV !exit !lhVal !ets =
  exitEdh ets exit
    =<< mkDefault''
      Nothing
      (ArgsPack [] $ odFromList [(AttrByName "lhv", lhVal)])
      (LitExpr NilLiteral)

intrinsicOpReturnDefault ::
  EdhTxExit EdhValue ->
  EdhValue ->
  EdhValue ->
  Expr ->
  EdhTx
intrinsicOpReturnDefault !exit !lhVal !rhVal !defExpr !ets =
  exitEdh ets exit
    =<< mkDefault'' (Just ets) (ArgsPack [lhVal, rhVal] odEmpty) defExpr

-- | operator (++) - string coercing concatenator
concatProc :: EdhIntrinsicOp
concatProc !lhExpr !rhExpr !exit !ets =
  runEdhTx ets $
    evalExprSrc lhExpr $ \ !lhVal ->
      evalExprSrc rhExpr $ \ !rhVal -> case edhUltimate lhVal of
        EdhString !lhStr -> case edhUltimate rhVal of
          EdhString !rhStr -> exitEdhTx exit $ EdhString $ lhStr <> rhStr
          _ -> defaultConvert lhVal rhVal
        EdhBlob !lhBlob -> case edhUltimate rhVal of
          EdhBlob !rhBlob -> exitEdhTx exit $ EdhBlob $ lhBlob <> rhBlob
          EdhString !rhStr ->
            exitEdhTx exit $ EdhBlob $ lhBlob <> TE.encodeUtf8 rhStr
          _ -> intrinsicOpReturnNA exit lhVal rhVal
        _ -> defaultConvert lhVal rhVal
  where
    isDefaulting !v = case edhUltimate v of
      EdhDefault {} -> True
      _ -> False
    defaultConvert :: EdhValue -> EdhValue -> EdhTx
    defaultConvert !lhVal !rhVal =
      if isDefaulting lhVal || isDefaulting rhVal
        then -- don't apply to defaulting values
          exitEdhTx exit edhNA
        else
          intrinsicOpReturnDefault exit lhVal rhVal $
            InfixExpr
              (OpSymSrc "++" noSrcRange)
              ( ExprSrc
                  ( CallExpr
                      ( ExprSrc
                          ( AttrExpr
                              ( DirectRef
                                  (AttrAddrSrc (NamedAttr "str") noSrcRange)
                              )
                          )
                          noSrcRange
                      )
                      ( ArgsPacker
                          [ SendPosArg
                              ( ExprSrc
                                  (LitExpr (ValueLiteral lhVal))
                                  noSrcRange
                              )
                          ]
                          noSrcRange
                      )
                  )
                  noSrcRange
              )
              ( ExprSrc
                  ( CallExpr
                      ( ExprSrc
                          ( AttrExpr
                              ( DirectRef
                                  (AttrAddrSrc (NamedAttr "str") noSrcRange)
                              )
                          )
                          noSrcRange
                      )
                      ( ArgsPacker
                          [ SendPosArg
                              ( ExprSrc
                                  (LitExpr (ValueLiteral rhVal))
                                  noSrcRange
                              )
                          ]
                          noSrcRange
                      )
                  )
                  noSrcRange
              )

-- | utility repr(val) - repr extractor
reprProc :: Expr -> EdhHostProc
reprProc !x !exit = evalExpr x $ \ !v -> edhValueReprTx v $ exit . EdhString

-- | utility str(val) - str extractor
strProc :: Expr -> EdhHostProc
strProc !x !exit = evalExpr x $ \ !v -> edhValueStrTx v $ exit . EdhString

capProc :: EdhValue -> RestKwArgs -> EdhHostProc
capProc !v !kwargs !exit = case edhUltimate v of
  EdhObject !o ->
    callMagicMethod o (AttrByName "__cap__") (ArgsPack [] kwargs) exit
  _ -> exitEdhTx exit $ EdhDecimal D.nan

growProc :: EdhValue -> Decimal -> RestKwArgs -> EdhHostProc
growProc !v !newCap !kwargs !exit = case edhUltimate v of
  EdhObject !o ->
    callMagicMethod
      o
      (AttrByName "__grow__")
      (ArgsPack [EdhDecimal newCap] kwargs)
      exit
  !badVal -> edhSimpleDescTx badVal $ \ !badDesc ->
    throwEdhTx UsageError $ "grow() not supported by: " <> badDesc

lenProc :: EdhValue -> RestKwArgs -> EdhHostProc
lenProc !v !kwargs !exit !ets = case edhUltimate v of
  EdhObject !o ->
    runEdhTx ets $
      callMagicMethod o (AttrByName "__len__") (ArgsPack [] kwargs) exit
  EdhList (List _ !lv) ->
    {- HLINT ignore "Redundant <$>" -}
    length <$> readTVar lv >>= \ !llen ->
      exitEdh ets exit $ EdhDecimal $ fromIntegral llen
  EdhDict (Dict _ !ds) ->
    iopdSize ds
      >>= \ !dlen -> exitEdh ets exit $ EdhDecimal $ fromIntegral dlen
  EdhArgsPack (ArgsPack !posArgs _kwArgs) ->
    -- assuming tuple semantics, return number of positional arguments
    exitEdh ets exit $ EdhDecimal $ fromIntegral $ length posArgs
  EdhString !txt ->
    -- though strings are not indexable/slicable yet
    exitEdh ets exit $ EdhDecimal $ fromIntegral $ T.length txt
  EdhBlob !bytes ->
    -- though blobs are not indexable/slicable yet
    exitEdh ets exit $ EdhDecimal $ fromIntegral $ B.length bytes
  _ -> exitEdh ets exit $ EdhDecimal D.nan

markProc :: EdhValue -> Decimal -> RestKwArgs -> EdhHostProc
markProc !v !newLen !kwargs !exit = case edhUltimate v of
  EdhObject !o ->
    callMagicMethod
      o
      (AttrByName "__mark__")
      (ArgsPack [EdhDecimal newLen] kwargs)
      exit
  !badVal ->
    throwEdhTx UsageError $
      "mark() not supported by a value of " <> edhTypeNameOf badVal

showProc :: Expr -> RestKwArgs -> EdhHostProc
showProc !x !kwExprs !exit !ets = runEdhTx ets $
  evalExpr x $ \ !v -> case v of
    EdhNamedValue !n !val -> edhValueReprTx val $
      \ !repr -> exitEdhTx exit $ EdhString $ n <> " := " <> repr
    _ -> case edhUltimate v of
      EdhObject !o -> evalKwExprs kwExprs $ \ !kwargs ->
        invokeMagic o (AttrByName "__show__") (ArgsPack [] kwargs) exit $
          \callAsMethod -> \case
            (_, EdhNil) -> runEdhTx ets $ showWithNoMagic v
            (_, s@EdhString {}) -> exitEdh ets exit s
            !magicArt -> callAsMethod magicArt
      EdhProcedure !callable Nothing ->
        exitEdhTx exit $
          EdhString $ T.pack (show callable)
      EdhProcedure !callable Just {} ->
        exitEdhTx exit $
          EdhString $ "effectful " <> T.pack (show callable)
      EdhBoundProc !callable _ _ Nothing ->
        exitEdhTx exit $
          EdhString $ "bound " <> T.pack (show callable)
      EdhBoundProc !callable _ _ Just {} ->
        exitEdhTx exit $
          EdhString $ "effectful bound " <> T.pack (show callable)
      -- todo specialize more informative show for intrinsic types of values
      _ -> showWithNoMagic v
  where
    showWithNoMagic v = edhValueReprTx v $ \ !s ->
      exitEdhTx exit $ EdhString $ edhTypeNameOf v <> ": " <> s

descProc :: Expr -> RestKwArgs -> EdhHostProc
descProc !x !kwExprs !exit !ets = runEdhTx ets $
  evalExpr x $ \ !v -> case edhUltimate v of
    EdhObject !o -> evalKwExprs kwExprs $ \ !kwargs ->
      invokeMagic o (AttrByName "__desc__") (ArgsPack [] kwargs) exit $
        \callAsMethod -> \case
          (_, EdhNil) -> runEdhTx ets $ descWithNoMagic v
          (_, s@EdhString {}) -> exitEdh ets exit s
          !magicArt -> callAsMethod magicArt
    EdhProcedure !callable Nothing ->
      exitEdhTx exit $
        EdhString $
          "It is a "
            <> T.pack (show callable)
            <> docString (callableDoc callable)
    EdhProcedure !callable Just {} ->
      exitEdhTx exit $
        EdhString $
          "It is an effectful "
            <> T.pack (show callable)
            <> docString (callableDoc callable)
    EdhBoundProc !callable _ _ Nothing ->
      exitEdhTx exit $
        EdhString $
          "It is a bound "
            <> T.pack (show callable)
            <> docString (callableDoc callable)
    EdhBoundProc !callable _ _ Just {} ->
      exitEdhTx exit $
        EdhString $
          "It is an effectful bound "
            <> T.pack (show callable)
            <> docString (callableDoc callable)
    -- TODO specialize more informative description (statistical wise) for
    --      intrinsic types of values
    _ -> descWithNoMagic v
  where
    descWithNoMagic v = edhValueDescTx v $ exitEdhTx exit . EdhString

    docString :: OptDocCmt -> Text
    -- todo process ReST formatting?
    docString NoDocCmt = ""
    docString (DocCmt !docCmt) =
      (("\n * doc comments *\n" <>) . T.unlines) docCmt

-- | utility null(val) - null tester
isNullProc :: Expr -> EdhHostProc
isNullProc !x !exit = evalExpr x $ \ !v !ets ->
  edhValueNull ets v $ exitEdh ets exit . EdhBool

-- | utility compare(v1, v2) - value comparator
cmpProc :: EdhValue -> EdhValue -> EdhHostProc
cmpProc !v1 !v2 !exit !ets = edhCompareValue ets v1 v2 $ \case
  Nothing -> exitEdh ets exit edhNA
  Just !conclusion -> exitEdh ets exit $ EdhOrd conclusion

-- | utility type(value) - value type introspector
typeProc :: Expr -> EdhHostProc
typeProc !valExpr !exit =
  evalExpr valExpr $ exitEdhTx exit . EdhString . edhTypeNameOf

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
    {- HLINT ignore "Use first" -}
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

listReverseProc :: List -> EdhHostProc
listReverseProc l@(List _ !lv) !exit !ets = do
  modifyTVar' lv reverse
  exitEdh ets exit $ EdhList l

listCopyProc :: List -> EdhHostProc
listCopyProc (List _ !lv) !exit !ets = do
  !u <- unsafeIOToSTM newUnique
  !lv' <- newTVar =<< readTVar lv
  exitEdh ets exit $ EdhList $ List u lv'

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
    let !lhv = edhDeFlowCtrl lhVal
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

-- | operator (/>) - list reverse prepender
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

-- | unzip utility - unzip a series of tuples from either a tuple, a list or
-- enumeration with a for-loop, into a tuple of tuples
unzipProc :: "tuples" !: Expr -> EdhHostProc
unzipProc (mandatoryArg -> !tuplesExpr) !exit !ets =
  case deParen' tuplesExpr of
    ForExpr !scoped !argsRcvr !iterExpr !bodyStmt -> do
      !stripsVar <- newTVar []
      edhPrepareForLoop
        ets
        scoped
        argsRcvr
        iterExpr
        bodyStmt
        ( \ !val -> case val of
            EdhArgsPack (ArgsPack !args !kwargs)
              | odNull kwargs ->
                modifyTVar' stripsVar $ log1 args
            _ -> edhSimpleDesc ets val $
              \ !badDesc ->
                throwEdh ets UsageError $
                  "element tuple expected from the unzip series, but given: "
                    <> badDesc
        )
        $ \_iterVal !runLoop -> runEdhTx ets $
          runLoop $ \_ _ets ->
            readTVar stripsVar
              >>= exitEdh ets exit . EdhArgsPack . flip ArgsPack odEmpty
                . fmap mkStrip
    _ -> runEdhTx ets $
      evalExpr tuplesExpr $ \ !tuplesVal _ets ->
        case edhUltimate tuplesVal of
          EdhArgsPack (ArgsPack !s !kwargs) | odNull kwargs ->
            unzipSeries s $ \ !strips ->
              exitEdh ets exit $
                EdhArgsPack $ ArgsPack (mkStrip <$> strips) odEmpty
          EdhList (List _u !sVar) -> do
            !s <- readTVar sVar
            unzipSeries s $ \ !strips ->
              exitEdh ets exit $
                EdhArgsPack $ ArgsPack (mkStrip <$> strips) odEmpty
          _ -> edhSimpleDesc ets tuplesVal $ \ !badDesc ->
            throwEdh ets UsageError $
              "unzip series should be a tuple or list, but given: "
                <> badDesc
  where
    unzipSeries :: [EdhValue] -> ([[EdhValue]] -> STM ()) -> STM ()
    unzipSeries s !exit' = go s []
      where
        go :: [EdhValue] -> [[EdhValue]] -> STM ()
        go [] strips = exit' strips
        go (v : rest) strips = case edhUltimate v of
          EdhArgsPack (ArgsPack !vs !kwargs)
            | odNull kwargs ->
              go rest $ log1 vs strips
          EdhList (List _u !vsVar) -> do
            !vs <- readTVar vsVar
            go rest $ log1 vs strips
          _ -> edhSimpleDesc ets v $ \ !badDesc ->
            throwEdh ets UsageError $
              "element tuple expected from the unzip series, but given: "
                <> badDesc

    log1 :: [EdhValue] -> [[EdhValue]] -> [[EdhValue]]
    log1 [] !strips = strips
    log1 (v : rest) [] = [v] : log1 rest []
    log1 (v : rest) (strip : strips) = (v : strip) : log1 rest strips

    mkStrip :: [EdhValue] -> EdhValue
    mkStrip vs = EdhArgsPack $ flip ArgsPack odEmpty $! reverse vs

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
  ForExpr !scoped !argsRcvr !iterExpr !bodyStmt ->
    evalExprSrc lhExpr $ \ !lhVal !ets ->
      case edhUltimate lhVal of
        EdhList (List _ !l) ->
          edhPrepareForLoop
            ets
            scoped
            argsRcvr
            iterExpr
            bodyStmt
            (\ !val -> modifyTVar' l (++ [edhNonNil val]))
            ( \_iterVal !runLoop ->
                runEdhTx ets $ runLoop $ \_ -> exitEdhTx exit lhVal
            )
        EdhDict (Dict _ !d) ->
          edhPrepareForLoop
            ets
            scoped
            argsRcvr
            iterExpr
            bodyStmt
            (\ !val -> insertToDict ets (edhNonNil val) d)
            ( \_iterVal !runLoop ->
                runEdhTx ets $ runLoop $ \_ -> exitEdhTx exit lhVal
            )
        EdhArgsPack (ArgsPack !args !kwargs) -> do
          !posArgs <- newTVar args
          !kwArgs <- iopdFromList $ odToList kwargs
          edhPrepareForLoop
            ets
            scoped
            argsRcvr
            iterExpr
            bodyStmt
            ( \ !val -> case val of
                EdhArgsPack (ArgsPack !args' !kwargs') -> do
                  modifyTVar' posArgs (++ args')
                  iopdUpdate (odToList kwargs') kwArgs
                _ -> modifyTVar' posArgs (++ [edhNonNil val])
            )
            $ \_iterVal !runLoop -> runEdhTx ets $
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
