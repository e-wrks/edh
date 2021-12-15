{-# LANGUAGE ImplicitParams #-}

module Language.Edh.Evaluate where

-- import Debug.Trace
-- import GHC.Stack

import Control.Applicative
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Control.Monad.State.Strict
import qualified Data.Aeson as A
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Data.Dynamic
import qualified Data.HashMap.Strict as Map
import Data.Hashable
import Data.IORef
import Data.List
import Data.Lossless.Decimal (Decimal (..))
import qualified Data.Lossless.Decimal as D
import Data.Maybe
import Data.Ratio
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (Decoding (Some))
import qualified Data.Text.Encoding as TE
import Data.Text.Encoding.Error (lenientDecode)
import qualified Data.UUID as UUID
import Deque.Lazy (Deque)
import qualified Deque.Lazy as Deque
import GHC.Clock
import GHC.Conc (forkIOWithUnmask, myThreadId, unsafeIOToSTM)
import GHC.Exts
import Language.Edh.Control
import Language.Edh.CoreLang
import Language.Edh.IOPD
import Language.Edh.Parser
import Language.Edh.PkgMan
import Language.Edh.RUID
import Language.Edh.RtTypes
import Language.Edh.Sink
import Language.Edh.Utils
import Numeric
import System.FilePath
import System.Posix
import Text.Megaparsec
  ( PosState (..),
    State (..),
    errorBundlePretty,
    runParserT',
  )
import Text.Megaparsec.Pos
  ( SourcePos (SourcePos, sourceColumn, sourceLine, sourceName),
    mkPos,
  )
import Type.Reflection
import Prelude

-- | Construct an error context from thread state
getEdhErrCtx :: Int -> EdhThreadState -> ErrContext
getEdhErrCtx !unwind !ets =
  T.unlines $
    reverse $
      prettyFrame
        <$> unwindStack unwind (edh'ctx'tip ctx : edh'ctx'stack ctx)
  where
    !ctx = edh'context ets

    -- @remind look here for how to pretty-show backtrace of Edh call stack
    prettyFrame :: EdhCallFrame -> ErrContext
    prettyFrame !frm =
      "📜 "
        <> procedureName (edh'scope'proc $ edh'frame'scope frm)
        <> " 👉 "
        <> prettySrcLoc (edh'exe'src'loc frm)

    unwindStack :: Int -> [EdhCallFrame] -> [EdhCallFrame]
    unwindStack c s | c <= 0 = s
    unwindStack _ [] = []
    unwindStack _ [f] = [f]
    unwindStack c (_ : s) = unwindStack (c - 1) s

edhCreateError :: Int -> EdhThreadState -> EdhErrorTag -> ArgsPack -> EdhError
edhCreateError !unwindDef !ets !tag (ArgsPack !args !kwargs) = case args of
  [EdhString !m] | odNull kwargs' -> createErr m nil
  (EdhString !m : args') -> createErr m $ case args' of
    [] | odNull kwargs' -> nil
    _ -> EdhArgsPack $ ArgsPack args' kwargs'
  _ -> createErr "❌" $ case args of
    [] | odNull kwargs' -> nil
    _ -> EdhArgsPack $ ArgsPack args kwargs'
  where
    createErr !msg !details =
      EdhError tag msg (toDyn details) $ getEdhErrCtx unwind ets
    (!maybeUnwind, !kwargs') = odTakeOut (AttrByName "unwind") kwargs
    !unwind = case maybeUnwind of
      Just (EdhDecimal d) -> case D.decimalToInteger d of
        Just !n -> fromIntegral n
        _ -> unwindDef
      _ -> unwindDef

edhValueAsAttrKey :: EdhThreadState -> EdhValue -> (AttrKey -> STM ()) -> STM ()
edhValueAsAttrKey !ets !keyVal !exit =
  let naExit = edhValueDesc ets keyVal $ \ !valDesc ->
        throwEdh ets EvalError $ "unexpected attribute key: " <> valDesc
   in edhValueAsAttrKey' ets keyVal naExit exit

edhValueAsAttrKey' ::
  EdhThreadState -> EdhValue -> STM () -> (AttrKey -> STM ()) -> STM ()
edhValueAsAttrKey' !ets !keyVal !naExit !exit = case edhUltimate keyVal of
  EdhString !attrName -> exit $ AttrByName attrName
  EdhSymbol !sym -> exit $ AttrBySym sym
  EdhExpr (ExprDefi _ (AttrExpr (DirectRef (AttrAddrSrc !addr _))) _) _ ->
    resolveEdhAttrAddr ets addr exit
  _ -> naExit

{-# INLINE edhValueAsAttrKey #-}

-- | Get an attribute value from a target expression.
--
-- The target would be an object in most common cases, but can be some type of
-- value with virtual attributes, then one can be get as well.
getEdhAttr ::
  ExprSrc ->
  AttrKey ->
  EdhTxExit EdhValue ->
  EdhTxExit EdhValue ->
  EdhTx
getEdhAttr fromExpr@(ExprSrc !x _) !key !exitNoAttr !exit !ets = case x of
  -- no magic layer laid over access via `this` ref
  AttrExpr ThisRef {} -> do
    let this = edh'scope'this scope
    runEdhTx ets $
      getObjProperty' this key (exitNoAttr $ EdhObject this) exit
  AttrExpr ThatRef {} -> do
    let that = edh'scope'that scope

    runEdhTx ets $
      getObjProperty' that key (exitNoAttr $ EdhObject that) exit
  AttrExpr SuperRef {} ->
    let !this = edh'scope'this scope
     in lookupEdhSuperAttr this key >>= \case
          (_, EdhNil) -> exitEdh ets exitNoAttr $ EdhObject this
          result -> runEdhTx ets $ realizeObjProperty this exit result
  _ -> runEdhTx ets $
    evalExprSrc fromExpr $ \ !fromVal _ets ->
      case edhUltimate fromVal of
        EdhObject !obj ->
          runEdhTx ets $
            getObjProperty' obj key (exitNoAttr $ EdhObject obj) exit
        -- getting attr from an apk
        EdhArgsPack (ArgsPack _ !kwargs) ->
          exitEdh ets exit $ odLookupDefault EdhNil key kwargs
        -- virtual attrs by magic method from context
        _ -> case key of
          AttrByName !attrName -> do
            let !magicName =
                  "__" <> edhTypeNameOf fromVal <> "_" <> attrName <> "__"
            lookupEdhCtxAttr scope (AttrByName magicName) >>= \case
              -- todo allow bound contextual magic method for virtual attr?
              EdhProcedure (EdhMethod !mth) _ ->
                runEdhTx ets $
                  callEdhMethod
                    (edh'scope'this scope)
                    (edh'scope'that scope)
                    mth
                    (ArgsPack [fromVal] odEmpty)
                    id
                    -- todo check and honor default expr returned to here?
                    exit
              _ -> exitEdh ets exitNoAttr fromVal
          _ -> exitEdh ets exitNoAttr fromVal
  where
    ctx = edh'context ets
    scope = contextScope ctx

getObjProperty :: Object -> AttrKey -> EdhTxExit EdhValue -> EdhTx
getObjProperty !obj !key !exit = getObjProperty' obj key naExit exit
  where
    naExit =
      throwEdhTx EvalError $
        "no such property `" <> attrKeyStr key <> "` from a `"
          <> objClassName obj
          <> "` object"

getObjProperty' :: Object -> AttrKey -> EdhTx -> EdhTxExit EdhValue -> EdhTx
getObjProperty' !obj !key naExit !exit !ets =
  runEdhTx ets $
    getObjAttrWithMagic' obj key naExit $
      realizeObjProperty obj exit

realizeObjProperty ::
  Object -> EdhTxExit EdhValue -> (Object, EdhValue) -> EdhTx
realizeObjProperty obj exit (ownerInst, val) = case val of
  EdhBoundProc (EdhDescriptor !getter _) !this !that _ ->
    callEdhMethod this that getter (ArgsPack [] odEmpty) id exit
  EdhProcedure (EdhDescriptor !getter _) _ ->
    callEdhMethod ownerInst obj getter (ArgsPack [] odEmpty) id exit
  EdhProcedure !callable !effOuter ->
    -- bind an unbound procedure to inferred `this` and `that`
    exitEdhTx exit $ EdhBoundProc callable ownerInst obj effOuter
  -- return a bound procedure intact
  EdhBoundProc {} -> exitEdhTx exit val
  -- not a callable, return as is
  _ -> exitEdhTx exit val

-- | Try get an attribute from an object, with magic from either a super or self
getObjAttrWithMagic ::
  Object ->
  AttrKey ->
  EdhTxExit (Object, EdhValue) ->
  EdhTx
getObjAttrWithMagic !obj !key =
  getObjAttrWithMagic' obj key $
    throwEdhTx EvalError $
      "no such attribute `" <> attrKeyStr key <> "` from a `"
        <> objClassName obj
        <> "` object"

-- | Try get an attribute from an object, with magic from either a super or self
getObjAttrWithMagic' ::
  Object ->
  AttrKey ->
  EdhTx ->
  EdhTxExit (Object, EdhValue) ->
  EdhTx
getObjAttrWithMagic' !obj !key exitNoAttr !exit = case edh'obj'store obj of
  -- class objects are magic providers, never magic consumers
  ClassStore {} -> \ !ets ->
    lookupEdhObjAttr obj key >>= \case
      (_, EdhNil) -> runEdhTx ets exitNoAttr
      (this, !val) -> exitEdh ets exit (this, val)
  -- give super objects the magical power to intercept attribute access on
  -- descendant objects, by intercepting the attr resolution
  _ -> trySuperMagic (AttrByName "(@<-)")
  where
    -- TODO support defaulting along the list of super objs?
    trySuperMagic :: AttrKey -> EdhTx
    trySuperMagic !magicSpell !ets =
      lookupEdhSuperAttr obj magicSpell >>= \case
        (_, EdhNil) -> runEdhTx ets trySelfMagic
        (!super, EdhProcedure (EdhMethod !magicMth) _) ->
          withMagicMethod super magicMth super obj
        (!super, EdhBoundProc (EdhMethod !magicMth) !this !that _) ->
          withMagicMethod super magicMth this that
        (_, !magicVal) ->
          throwEdh ets UsageError $
            "invalid magic (spell= " <> attrKeyStr magicSpell
              <> ") method type: "
              <> edhTypeNameOf magicVal
      where
        withMagicMethod :: Object -> ProcDefi -> Object -> Object -> STM ()
        withMagicMethod !super !magicMth !this !that =
          runEdhTx ets $
            callEdhMethod
              this
              that
              magicMth
              (ArgsPack [attrKeyValue key] odEmpty)
              id
              $ \ !magicRtn _ets -> case edhUltimate magicRtn of
                EdhDefault _ _ !exprDef !etsDef ->
                  runEdhTx (fromMaybe ets etsDef) $
                    evalExpr (deExpr' exprDef) $
                      \ !defVal _ets -> case defVal of
                        EdhNil -> runEdhTx ets trySelfMagic
                        _ -> exitEdh ets exit (super, defVal)
                -- note don't bind a magic method here
                _ -> exitEdh ets exit (super, magicRtn)

    trySelfMagic :: EdhTx
    trySelfMagic !ets =
      lookupEdhObjAttr obj key >>= \case
        (_, EdhNil) -> readTVar (edh'obj'supers obj) >>= trySelves . (obj :)
        (this, !val) -> exitEdh ets exit (this, val)
      where
        trySelves :: [Object] -> STM ()
        trySelves [] = runEdhTx ets exitNoAttr
        trySelves (o : rest) =
          lookupEdhSelfMagic o (AttrByName "(@)") >>= \case
            EdhNil -> trySelves rest
            EdhProcedure (EdhMethod !mth) _ -> callSelfMagic mth o obj
            EdhBoundProc (EdhMethod !mth) !this !that _ ->
              callSelfMagic mth this that
            -- todo honor default expr here?
            !magicVal ->
              throwEdh ets UsageError $
                "invalid magic method type: " <> edhTypeNameOf magicVal
        callSelfMagic :: ProcDefi -> Object -> Object -> STM ()
        callSelfMagic !magicMth !this !that =
          runEdhTx ets $
            callEdhMethod
              this
              that
              magicMth
              (ArgsPack [attrKeyValue key] odEmpty)
              id
              $ \ !magicRtn _ets -> case edhUltimate magicRtn of
                EdhDefault _ _ !exprDef !etsDef ->
                  runEdhTx (fromMaybe ets etsDef) $
                    evalExpr (deExpr' exprDef) $
                      \ !defVal _ets -> chkMagicExit defVal
                _ -> chkMagicExit magicRtn
          where
            chkMagicExit :: EdhValue -> STM ()
            chkMagicExit = \case
              EdhNil -> runEdhTx ets exitNoAttr
              -- todo honor properties from self magic here?
              -- note don't bind for a val from self magic here
              !magicRtn -> exitEdh ets exit (this, magicRtn)

-- | Set an attribute value to a target expression.
--
-- The target would be an object in most common cases, but can be some type of
-- value with virtual attributes, but currently all virtual attributes are
-- readonly, not mutable virtual attribute supported yet.
setEdhAttr ::
  Expr ->
  AttrKey ->
  EdhValue ->
  EdhTxExit (Maybe Object, EdhValue) ->
  EdhTx
setEdhAttr !tgtExpr !key !val !exit !ets = case tgtExpr of
  -- no magic layer laid over assignment via `this` ref
  AttrExpr ThisRef {} ->
    let !this = edh'scope'this scope
     in setObjAttr ets this key val $
          \ !valSet -> exitEdh ets exit (Just this, valSet)
  -- no magic layer laid over assignment via `that` ref
  AttrExpr ThatRef {} ->
    let !that = edh'scope'that scope
     in setObjAttr ets that key val $
          \ !valSet -> exitEdh ets exit (Just that, valSet)
  -- not allowing assignment via super
  AttrExpr SuperRef {} -> throwEdh ets EvalError "can not assign via super"
  _ -> runEdhTx ets $
    evalExpr' tgtExpr NoDocCmt $ \ !tgtVal _ets ->
      case tgtVal of
        -- give super objects the magical power to intercept
        -- attribute assignment to descendant objects, via obj ref
        EdhObject !tgtObj ->
          runEdhTx ets $ setObjAttrWithMagic tgtObj key val exit
        -- no virtual attribute supported yet
        _ -> edhSimpleDesc ets tgtVal $ \ !badDesc ->
          throwEdh ets EvalError $ "invalid assignment target, " <> badDesc
  where
    ctx = edh'context ets
    scope = contextScope ctx

setObjAttrWithMagic ::
  Object ->
  AttrKey ->
  EdhValue ->
  EdhTxExit (Maybe Object, EdhValue) ->
  EdhTx
setObjAttrWithMagic !obj !key !val !exit !ets =
  trySuperMagic (AttrByName "(<-@)")
  where
    trySuperMagic :: AttrKey -> STM ()
    trySuperMagic !magicSpell =
      lookupEdhSuperAttr obj magicSpell >>= \case
        (_, EdhNil) -> trySelfMagic
        (!super, EdhProcedure (EdhMethod !magicMth) _) ->
          withMagicMethod magicMth super obj
        (_, EdhBoundProc (EdhMethod !magicMth) !this !that _) ->
          withMagicMethod magicMth this that
        (_, !magicVal) ->
          throwEdh ets UsageError $
            "invalid magic method type: " <> edhTypeNameOf magicVal
      where
        withMagicMethod :: ProcDefi -> Object -> Object -> STM ()
        withMagicMethod !magicMth !this !that =
          runEdhTx ets $
            callEdhMethod
              this
              that
              magicMth
              (ArgsPack [attrKeyValue key, val] odEmpty)
              id
              $ \ !magicRtn _ets -> case edhUltimate magicRtn of
                EdhDefault _ _ !exprDef !etsDef ->
                  runEdhTx (fromMaybe ets etsDef) $
                    evalExpr (deExpr' exprDef) $
                      \ !defVal _ets -> case defVal of
                        EdhNil -> trySelfMagic
                        _ -> exitEdh ets exit (Just obj, defVal)
                -- nil return value from super magic method, assuming attr set
                EdhNil ->
                  exitEdh
                    ets
                    exit
                    (Just obj, EdhNamedValue "<magic-set>" EdhNil)
                _ -> exitEdh ets exit (Just obj, magicRtn)

    trySelfMagic :: STM ()
    trySelfMagic = setObjProperty ets obj key val tryMagic $
      \ !valSet -> exitEdh ets exit (Just obj, valSet)
      where
        tryMagic :: STM ()
        tryMagic = readTVar (edh'obj'supers obj) >>= trySelves . (obj :)
        trySelves :: [Object] -> STM ()
        trySelves [] =
          writeObjAttr ets obj key val $
            \ !valSet -> exitEdh ets exit (Just obj, valSet)
        trySelves (o : rest) =
          lookupEdhSelfMagic o (AttrByName "(@=)") >>= \case
            EdhNil -> trySelves rest
            EdhProcedure (EdhMethod !mth) _ -> callSelfMagic mth o obj
            EdhBoundProc (EdhMethod !mth) !this !that _ ->
              callSelfMagic mth this that
            -- todo honor default expr here?
            !magicVal ->
              throwEdh ets UsageError $
                "invalid magic method type: " <> edhTypeNameOf magicVal
        callSelfMagic :: ProcDefi -> Object -> Object -> STM ()
        callSelfMagic !magicMth !this !that =
          let !args =
                if val == EdhNil
                  then [attrKeyValue key]
                  else [attrKeyValue key, val]
           in runEdhTx ets $
                callEdhMethod this that magicMth (ArgsPack args odEmpty) id $
                  \ !magicRtn _ets -> case edhUltimate magicRtn of
                    EdhDefault {} -> writeObjAttr ets that key val $
                      \ !valSet -> exitEdh ets exit (Just that, valSet)
                    _ -> exitEdh ets exit (Just that, magicRtn)

-- | Overwrite an attribute value of an object
--
-- A property with the same identifier will be overwritten
--
-- A new attribute will be created if not present previously
writeObjAttr ::
  EdhThreadState ->
  Object ->
  AttrKey ->
  EdhValue ->
  (EdhValue -> STM ()) ->
  STM ()
writeObjAttr !ets !obj !key !val !exit = case edh'obj'store obj of
  HashStore !hs -> iopdInsert key val hs >> exit val
  ClassStore !cls -> iopdInsert key val (edh'class'arts cls) >> exit val
  HostStore _ ->
    throwEdh ets UsageError $
      "can not write attribute `"
        <> T.pack (show key)
        <> "` to a host object of class "
        <> objClassName obj

-- | Set an attribute value of an object
--
-- A property setter will be invoked if present, if only a property getter is
-- present, an 'UsageError' will be thrown due to the property being readonly
--
-- A new attribute will be created if not present previously
setObjAttr ::
  EdhThreadState ->
  Object ->
  AttrKey ->
  EdhValue ->
  (EdhValue -> STM ()) ->
  STM ()
setObjAttr !ets !obj !key !val !exit =
  setObjProperty ets obj key val (writeObjAttr ets obj key val exit) exit

-- | Set a property value of an object
--
-- A property setter will be invoked if present, if only a property getter is
-- present, an 'UsageError' will be thrown due to the property being readonly
--
-- The 'naExit' continuation will be taken if no property descriptor present
setObjProperty ::
  EdhThreadState ->
  Object ->
  AttrKey ->
  EdhValue ->
  STM () ->
  (EdhValue -> STM ()) ->
  STM ()
setObjProperty !ets !obj !key !val !naExit !exit =
  lookupEdhObjAttr obj key >>= \case
    (_, EdhNil) -> naExit
    (!this', EdhProcedure (EdhDescriptor _getter (Just !setter)) _) ->
      callSetter this' obj setter
    (_, EdhBoundProc (EdhDescriptor _getter (Just !setter)) this that _) ->
      callSetter this that setter
    (!owner, EdhProcedure (EdhDescriptor !getter Nothing) _) ->
      readonly owner getter
    (!owner, EdhBoundProc (EdhDescriptor !getter Nothing) _ _ _) ->
      readonly owner getter
    _ -> naExit
  where
    callSetter !this !that !setter =
      let !args = case val of
            EdhNil -> []
            _ -> [val]
       in runEdhTx ets $
            callEdhMethod this that setter (ArgsPack args odEmpty) id $
              \ !propRtn _ets -> exit propRtn
    readonly !owner !getter =
      throwEdh ets UsageError $
        "property `"
          <> T.pack (show $ edh'procedure'name getter)
          <> "` of class "
          <> objClassName owner
          <> " is readonly"

-- | Assign an evaluated value to a target expression
assignEdhTarget :: Expr -> EdhValue -> EdhTxExit EdhValue -> EdhTx
assignEdhTarget !lhExpr !rhVal !exit !ets = case lhExpr of
  -- attribute assignment
  AttrExpr !addr -> case addr of
    -- silently drop value assigned to single underscore
    DirectRef (AttrAddrSrc (NamedAttr "_") _) -> exitEdh ets exit nil
    -- assign as attribute of local scope
    DirectRef (AttrAddrSrc !addr' _) ->
      resolveEdhAttrAddr ets addr' $ \ !key -> do
        case edh'ctx'eff'target ctx of
          Nothing -> iopdInsert key rhVal esScope
          Just !esEffs -> iopdInsert key rhVal esEffs
        exitWithChkExportTo (edh'scope'this scope) key rhVal
    -- exporting within a method procedure actually adds the artifact to
    -- its owning object's export store, besides changing the mth proc's
    -- scope, maybe confusing in some cases, need more thoughts on it

    -- special case, assigning with `this.v=x` `that.v=y`, handle exports
    -- todo err out if in effecting context?
    IndirectRef (ExprSrc (AttrExpr ThisRef {}) _) (AttrAddrSrc !addr' _) ->
      let this = edh'scope'this scope
       in resolveEdhAttrAddr ets addr' $ \ !key ->
            setObjAttr ets this key rhVal $
              \ !valSet -> exitWithChkExportTo this key valSet
    IndirectRef (ExprSrc (AttrExpr ThatRef {}) _) (AttrAddrSrc !addr' _) ->
      let that = edh'scope'that scope
       in resolveEdhAttrAddr ets addr' $ \ !key ->
            setObjAttr ets that key rhVal $
              \ !valSet -> exitWithChkExportTo that key valSet
    -- assign to an addressed attribute
    IndirectRef (ExprSrc !tgtExpr _) (AttrAddrSrc !addr' _) ->
      resolveEdhAttrAddr ets addr' $ \ !key ->
        runEdhTx ets $ setEdhAttr tgtExpr key rhVal $ exitMaybeExpTo key
    -- god forbidden things
    ThisRef {} -> throwEdh ets EvalError "can not assign to this"
    ThatRef {} -> throwEdh ets EvalError "can not assign to that"
    SuperRef {} -> throwEdh ets EvalError "can not assign to super"
  -- dereferencing attribute assignment
  InfixExpr (OpSymSrc "@" _) (ExprSrc !tgtExpr _) (ExprSrc !addrRef _) ->
    runEdhTx ets $
      evalExpr' addrRef NoDocCmt $ \ !addrVal _ets ->
        case edhUltimate addrVal of
          EdhExpr
            (ExprDefi _ (AttrExpr (DirectRef (AttrAddrSrc !addr _))) _)
            _ -> resolveEdhAttrAddr ets addr $ \ !key ->
              runEdhTx ets $ setEdhAttr tgtExpr key rhVal $ exitMaybeExpTo key
          EdhString !attrName -> do
            let !key = AttrByName attrName
            runEdhTx ets $ setEdhAttr tgtExpr key rhVal $ exitMaybeExpTo key
          EdhSymbol !sym -> do
            let !key = AttrBySym sym
            runEdhTx ets $ setEdhAttr tgtExpr key rhVal $ exitMaybeExpTo key
          _ ->
            throwEdh ets EvalError $
              "invalid attribute reference type - " <> edhTypeNameOf addrVal
  _ -> methodArrowArgsReceiver (deParen'1 lhExpr) $ \case
    -- todo allow indirect refs etc. as multi-assignment targets
    Left _err ->
      throwEdh ets EvalError $
        "invalid left hand expression for assignment: " <> T.pack (show lhExpr)
    Right !argsRcvr -> do
      let apk = case edhUltimate rhVal of
            EdhArgsPack k -> deApk k
            _ -> ArgsPack [rhVal] odEmpty
      recvEdhArgs ets ctx argsRcvr apk $ \ !um -> do
        case edh'ctx'eff'target ctx of
          Nothing ->
            -- normal multi-assignment
            iopdUpdate (odToList um) (edh'scope'entity scope)
          Just !esEffs ->
            -- define effectful artifacts by multi-assignment
            -- note that nil can not appear as for arg receiving,
            -- so no processing of delete semantics
            iopdUpdate (odToList um) esEffs
        case edh'ctx'exp'target ctx of
          Nothing -> pure ()
          Just !esExps ->
            -- note that nil can not appear as for arg receiving,
            -- so no processing of delete semantics
            iopdUpdate (odToList um) esExps
        exitEdh ets exit rhVal
  where
    !ctx = edh'context ets
    scope = contextScope ctx
    esScope = edh'scope'entity scope

    exitMaybeExpTo :: AttrKey -> EdhTxExit (Maybe Object, EdhValue)
    exitMaybeExpTo !key (!maybeOwner, !valSet) = case maybeOwner of
      Just !o -> \_ets -> exitWithChkExportTo o key valSet
      _ -> exitEdhTx exit valSet

    exitWithChkExportTo :: Object -> AttrKey -> EdhValue -> STM ()
    exitWithChkExportTo !obj !artKey !artVal =
      case edh'ctx'exp'target ctx of
        Nothing -> exitEdh ets exit artVal
        Just _esExps -> prepareExpStore ets obj $ \ !esExps -> do
          iopdInsert artKey artVal esExps
          exitEdh ets exit artVal

prepareExpStore ::
  EdhThreadState -> Object -> (EntityStore -> STM ()) -> STM ()
prepareExpStore !ets !fromObj = prepareExpStore' ets fromObj $ do
  throwEdh ets EvalError $
    "no way exporting with a host object of class " <> objClassName fromObj

prepareExpStore' ::
  EdhThreadState -> Object -> STM () -> (EntityStore -> STM ()) -> STM ()
prepareExpStore' !ets !fromObj !naExit !exit = case edh'obj'store fromObj of
  HashStore !tgtEnt -> fromStore tgtEnt
  ClassStore !cls -> fromStore $ edh'class'arts cls
  HostStore _ -> naExit
  where
    fromStore tgtEnt =
      (exit =<<) $
        prepareMagicStore (AttrByName edhExportsMagicName) tgtEnt $
          edhCreateNsObj ets NoDocCmt phantomHostProc $ AttrByName "export"

prepareEffStore :: EdhThreadState -> EntityStore -> STM EntityStore
prepareEffStore = prepareEffStore' $ AttrByName edhEffectsMagicName

prepareEffStore' :: AttrKey -> EdhThreadState -> EntityStore -> STM EntityStore
prepareEffStore' !magicKey !ets !tgtEnt =
  prepareMagicStore magicKey tgtEnt $
    edhCreateNsObj ets NoDocCmt phantomHostProc $ AttrByName "effect"

phantomHostProc :: ProcDecl
phantomHostProc = HostDecl $ \_apk _exit ->
  throwEdhTx EvalError "bug: calling phantom procedure"

phantomAllocator :: ArgsPack -> EdhObjectAllocator
phantomAllocator _ _ !ets =
  throwEdh ets EvalError "bug: allocating phantom object"

edhCreateNsObj ::
  EdhThreadState ->
  OptDocCmt ->
  ProcDecl ->
  AttrKey ->
  EntityStore ->
  STM Object
edhCreateNsObj !ets !docCmt !pd !nsName !nsStore = do
  !idNs <- newRUID'STM
  !ss <- newTVar []
  let !nsProc =
        ProcDefi
          { edh'procedure'ident = idNs,
            edh'procedure'name = nsName,
            edh'procedure'lexi = scope,
            edh'procedure'doc = docCmt,
            edh'procedure'decl = pd
          }
      !nsObj =
        Object
          (HashStore nsStore)
          nsClsObj
            { edh'obj'store = ClassStore nsClass {edh'class'proc = nsProc}
            }
          ss
  return nsObj
  where
    !ctx = edh'context ets
    !scope = contextScope ctx
    !rootScope = edh'world'root $ edh'prog'world $ edh'thread'prog ets
    !nsClsObj = edh'obj'class $ edh'scope'this rootScope
    !nsClass = case edh'obj'store nsClsObj of
      ClassStore !cls -> cls
      _ -> error "bug: namespace class not bearing ClassStore"

-- | Create an Edh host object from the specified class and host data
--
-- note the caller is responsible to make sure the supplied host data
-- is compatible with the class
edhCreateHostObj ::
  forall v. (Eq v, Hashable v, Typeable v) => Object -> v -> STM Object
edhCreateHostObj !clsObj !hd = edhCreateHostObj' clsObj (wrapHostValue hd) []

-- | Create an Edh host object from the specified class, host storage data and
-- list of super objects.
--
-- note the caller is responsible to make sure the supplied host storage data
-- is compatible with the class, the super objects are compatible with the
-- class' mro.
edhCreateHostObj' :: Object -> HostValue -> [Object] -> STM Object
edhCreateHostObj' !clsObj !hsd !supers = do
  !ss <- newTVar supers
  return $ Object (HostStore hsd) clsObj ss

-- | Construct an Edh object from a class.
edhConstructObj :: Object -> ArgsPack -> (Object -> EdhTx) -> EdhTx
edhConstructObj !clsObj !apk !exit !ets = do
  !instMap <- newTVar Map.empty
  case edh'obj'store clsObj of
    ClassStore !endClass -> do
      let createOne ::
            Object -> [Object] -> ArgsPack -> (Object -> STM ()) -> STM ()
          createOne !co !restSupers !apkCtor !exitOne =
            case edh'obj'store co of
              ClassStore !cls ->
                reformCtorArgs co cls apkCtor $ \ !apkCtor' -> do
                  let allocIt :: STM ()
                      allocIt = do
                        !mro <- readTVar (edh'class'mro cls)
                        !im <- readTVar instMap
                        case sequence $
                          (\ !sco -> fst <$> Map.lookup sco im)
                            <$> mro of
                          Nothing ->
                            throwEdh
                              ets
                              EvalError
                              "bug: missing some instance by mro"
                          Just !supers -> do
                            let !ctx = edh'context ets
                                !tip = edh'ctx'tip ctx
                                !etsAlloc =
                                  ets
                                    { edh'context =
                                        ctx
                                          { -- stack the tip frame one more time up, so effectful artifacts
                                            -- directly in caller's scope are available during allocation
                                            edh'ctx'tip = tip,
                                            edh'ctx'stack = tip : edh'ctx'stack ctx,
                                            -- discourage artifact definition during allocation
                                            edh'ctx'pure = True
                                          }
                                    }
                            runEdhTx etsAlloc $
                              edh'class'allocator cls apkCtor' $ \ !os -> do
                                !ss <- newTVar supers
                                let !o = Object os co ss
                                -- put into instance map by class
                                modifyTVar' instMap $ Map.insert co (o, apkCtor')
                                exitOne o
                  case restSupers of
                    [] -> allocIt
                    (nextSuper : restSupers') ->
                      createOne nextSuper restSupers' apkCtor' $ const allocIt
              _ -> throwEdh ets EvalError "bug: non-class object in mro"
      !superClasses <- readTVar (edh'class'mro endClass)
      createOne clsObj superClasses apk $ \ !obj -> do
        !im <- readTVar instMap
        let callInit :: [Object] -> STM () -> STM ()
            callInit [] !initExit = initExit
            callInit (o : rest) !initExit =
              case Map.lookup (edh'obj'class o) im of
                Nothing -> throwEdh ets EvalError "bug: ctor apk missing"
                Just (_o, !apkCtor') ->
                  callInit rest $
                    lookupEdhSelfMagic o (AttrByName "__init__")
                      >>= \case
                        EdhNil -> initExit
                        EdhProcedure (EdhMethod !mthInit) _ ->
                          runEdhTx ets $
                            callEdhMethod o obj mthInit apkCtor' id $
                              \_initResult _ets -> initExit
                        EdhBoundProc (EdhMethod !mthInit) !this !that _ ->
                          runEdhTx ets $
                            callEdhMethod this that mthInit apkCtor' id $
                              \_initResult _ets -> initExit
                        !badInitMth ->
                          edhSimpleDesc ets badInitMth $ \ !badDesc ->
                            throwEdh ets UsageError $
                              "invalid __init__ method on class "
                                <> objClassName o
                                <> " - "
                                <> badDesc
        !supers <- readTVar $ edh'obj'supers obj
        callInit (obj : supers) $ runEdhTx ets $ exit obj
    _ ->
      throwEdh ets UsageError $
        "can not create new object from a non-class object, which is a: "
          <> objClassName clsObj
  where
    reformCtorArgs ::
      Object -> Class -> ArgsPack -> (ArgsPack -> STM ()) -> STM ()
    reformCtorArgs !co !cls !apkCtor !exit' =
      iopdLookup (AttrByName "__reform_ctor_args__") (edh'class'arts cls)
        >>= \case
          Nothing -> exit' apkCtor
          Just (EdhProcedure (EdhMethod !mth) _) ->
            runEdhTx ets $
              callEdhMethod co clsObj mth apkCtor id $
                \ !magicRtn _ets -> case edhUltimate magicRtn of
                  EdhArgsPack !apkReformed -> exit' apkReformed
                  _ -> edhSimpleDesc ets magicRtn $ \ !badDesc ->
                    throwEdh ets UsageError $
                      "invalid return from __reform_ctor_args__ magic: "
                        <> badDesc
          Just !badMagicVal -> edhSimpleDesc ets badMagicVal $ \ !badDesc ->
            throwEdh ets UsageError $
              "bad __reform_ctor_args__ magic: "
                <> badDesc

-- Clone a composite object with one of its object instance `mutObj` mutated
-- to bear the new host storage data
--
-- Other member instances are either deep-cloned as class based super, or left
-- intact as prototype based super
--
-- todo maybe check new storage data type matches the old one?
edhCloneHostObj ::
  (Eq v, Hashable v, Typeable v) =>
  EdhThreadState ->
  Object ->
  Object ->
  v ->
  (Object -> STM ()) ->
  STM ()
edhCloneHostObj !ets !endObj !mutObj !newData !exit =
  edhMutCloneObj ets mutObj endObj (HostStore $ wrapHostValue newData) exit

-- Clone a composite object with one of its object instance `mutObj` mutated
-- to bear the new object stroage
--
-- Other member instances are either deep-cloned as class based super, or left
-- intact as prototype based super
edhMutCloneObj ::
  EdhThreadState ->
  Object ->
  Object ->
  ObjectStore ->
  (Object -> STM ()) ->
  STM ()
edhMutCloneObj !ets !endObj !mutObj !newStore !exitEnd =
  newTVar Map.empty >>= \ !instMap ->
    let cloneSupers ::
          [Object] -> [Object] -> [Object] -> ([Object] -> STM ()) -> STM ()
        cloneSupers !cloned [] _ !exitSupers =
          exitSupers $ reverse cloned
        cloneSupers !cloned supers [] !exitSupers =
          -- no corresponding class from mro, the rest supers are prototype
          -- instances extended individually, don't clone them
          exitSupers $ reverse cloned ++ supers
        cloneSupers !cloned (super : rest) (superCls : restCls) !exitSupers =
          {- HLINT ignore "Redundant <$>" -}
          if edh'obj'class super /= superCls
            then throwEdh ets EvalError "bug: super instance unaligned with mro"
            else
              Map.lookup super <$> readTVar instMap >>= \case
                Just !superClone ->
                  cloneSupers (superClone : cloned) rest restCls exitSupers
                Nothing -> clone1 super $ \ !superClone ->
                  cloneSupers (superClone : cloned) rest restCls exitSupers
        clone1 :: Object -> (Object -> STM ()) -> STM ()
        clone1 !obj !exit1 = do
          !mro <- readTVar $ edh'class'mro $ objClass obj
          !supers <- readTVar (edh'obj'supers obj)
          cloneSupers [] supers mro $
            \ !supersClone -> do
              !supersNew <- newTVar supersClone
              !objClone <-
                if obj == mutObj
                  then
                    return
                      mutObj
                        { edh'obj'store = newStore,
                          edh'obj'supers = supersNew
                        }
                  else case edh'obj'store obj of
                    HashStore !es -> do
                      !es' <- iopdClone es
                      let !objClone =
                            obj
                              { edh'obj'store = HashStore es',
                                edh'obj'supers = supersNew
                              }
                      return objClone
                    ClassStore !cls -> do
                      !cs' <- iopdClone $ edh'class'arts cls
                      let !clsClone =
                            obj
                              { edh'obj'store =
                                  ClassStore
                                    cls
                                      { edh'class'arts = cs'
                                      },
                                edh'obj'supers = supersNew
                              }
                      return clsClone
                    HostStore !hsd -> do
                      let !objClone =
                            obj
                              { edh'obj'store = HostStore hsd,
                                edh'obj'supers = supersNew
                              }
                      return objClone
              modifyTVar' instMap $ Map.insert obj objClone
              lookupEdhSelfMagic objClone (AttrByName "__clone__") >>= \case
                EdhNil -> exit1 objClone
                EdhProcedure (EdhMethod !mth) _ ->
                  runEdhTx ets $
                    callEdhMethod
                      objClone
                      endObj
                      mth
                      (ArgsPack [] odEmpty)
                      id
                      $ \_ _ets -> exit1 objClone
                EdhBoundProc (EdhMethod _mth) _this _that _ ->
                  throwEdh
                    ets
                    UsageError
                    "a bound __clone__ method, assumed wrong, discussion?"
                !badMth ->
                  throwEdh ets UsageError $
                    "invalid __clone__ method of type: "
                      <> edhTypeNameOf badMth
     in clone1 endObj $ \ !thatNew -> exitEnd thatNew

edhObjExtends :: EdhThreadState -> Object -> Object -> STM () -> STM ()
edhObjExtends !ets !this !superObj !exit = case edh'obj'store this of
  ClassStore {} -> case edh'obj'store superObj of
    ClassStore {} -> doExtends
    _ -> throwEdh ets UsageError "a class object can not extend a non-class"
  _ -> doExtends
  where
    doExtends = do
      modifyTVar' (edh'obj'supers this) (++ [superObj])
      lookupEdhSelfMagic superObj magicSpell >>= \case
        EdhNil -> exit
        !magicMth -> runEdhTx ets $ withMagicMethod magicMth

    !magicSpell = AttrByName "<-^"

    callMagicMth !mthThis !mthThat !mth =
      objectScope this >>= \ !objScope ->
        do
          !scopeObj <- mkScopeWrapper ets objScope
          runEdhTx ets $
            callEdhMethod
              mthThis
              mthThat
              mth
              (ArgsPack [EdhObject scopeObj] odEmpty)
              id
              $ \_magicRtn _ets -> exit

    withMagicMethod :: EdhValue -> EdhTx
    withMagicMethod !magicMth _ets = case magicMth of
      EdhNil -> exit
      EdhProcedure (EdhMethod !mth) _ -> callMagicMth superObj this mth
      -- even if it's already bound, should use `this` here as
      -- contextual `that` there
      EdhBoundProc (EdhMethod !mth) !mthThis _mthThat _ ->
        callMagicMth mthThis this mth
      _ ->
        throwEdh ets EvalError $
          "invalid magic (<-^) method type: " <> edhTypeNameOf magicMth

callEdhOperator ::
  Object ->
  Object ->
  ProcDefi ->
  Maybe EdhValue ->
  [EdhValue] ->
  EdhTxExit EdhValue ->
  EdhTx
callEdhOperator !this !that !mth !prede !args !exit =
  case edh'procedure'decl mth of
    -- calling a host operator procedure
    HostDecl !hp -> \ !ets -> do
      -- a host procedure views the same scope entity as of the caller's
      -- call frame
      let !callerCtx = edh'context ets
          !callerScope = contextScope callerCtx

          !mthScope =
            Scope
              { edh'scope'entity = edh'scope'entity callerScope,
                edh'scope'this = this,
                edh'scope'that = that,
                edh'scope'proc = mth,
                edh'effects'stack = []
              }
      !tipFrame <-
        newCallFrame mthScope (SrcLoc (SrcDoc "<intrinsic>") noSrcRange)
      let !mthCtx =
            callerCtx
              { edh'ctx'tip = tipFrame,
                edh'ctx'stack = edh'ctx'tip callerCtx : edh'ctx'stack callerCtx,
                edh'ctx'genr'caller = Nothing,
                edh'ctx'match = true,
                edh'ctx'pure = False,
                edh'ctx'exp'target = Nothing,
                edh'ctx'eff'target = Nothing
              }
          !etsMth = ets {edh'context = mthCtx}
      runEdhTx etsMth $
        hp (ArgsPack args odEmpty) $ \ !hpRtn ->
          -- a host operator is responsible to not return meaningless values
          -- like return wrapper, or e.g. continue/break etc.
          edhSwitchState ets $ exitEdhTx exit hpRtn

    -- calling an Edh operator procedure
    ProcDecl _ _ _ !pb !pl ->
      callEdhOperator' this that mth prede pl pb args exit

callEdhOperator' ::
  Object ->
  Object ->
  ProcDefi ->
  Maybe EdhValue ->
  SrcLoc ->
  StmtSrc ->
  [EdhValue] ->
  EdhTxExit EdhValue ->
  EdhTx
callEdhOperator'
  !this
  !that
  !mth
  !prede
  !proc'loc
  (StmtSrc !body'stmt _)
  !args
  !exit
  !ets =
    do
      !recvTipFrame <-
        newCallFrame
          (edh'procedure'lexi mth)
            { edh'scope'this = this,
              edh'scope'that = that
            }
          proc'loc
      let !recvCtx =
            callerCtx
              { edh'ctx'tip = recvTipFrame,
                edh'ctx'stack = new'stack,
                edh'ctx'genr'caller = Nothing,
                edh'ctx'match = true,
                edh'ctx'pure = False,
                edh'ctx'exp'target = Nothing,
                edh'ctx'eff'target = Nothing
              }
      recvEdhArgs
        ets
        recvCtx
        (edh'procedure'args $ edh'procedure'decl mth)
        (ArgsPack args odEmpty)
        $ \ !ed -> do
          !es <- iopdFromList $ odToList ed
          let !mthScope =
                Scope
                  { edh'scope'entity = es,
                    edh'scope'this = this,
                    edh'scope'that = that,
                    edh'scope'proc = mth,
                    edh'effects'stack = []
                  }
          !tipFrame <- newCallFrame mthScope proc'loc
          let !mthCtx =
                callerCtx
                  { edh'ctx'tip = tipFrame,
                    edh'ctx'stack = new'stack,
                    edh'ctx'genr'caller = Nothing,
                    edh'ctx'match = true,
                    edh'ctx'pure = False,
                    edh'ctx'exp'target = Nothing,
                    edh'ctx'eff'target = Nothing
                  }
              !etsMth = ets {edh'context = mthCtx}
          case prede of
            Nothing -> pure ()
            -- put the overridden predecessor operator into the overriding
            -- operator procedure's runtime scope
            Just !predOp -> iopdInsert (edh'procedure'name mth) predOp es
          runEdhTx etsMth $
            evalStmt body'stmt $ \ !bodyResult ->
              edhSwitchState ets $
                exitEdhTx exit $ case edhDeFlowCtrl bodyResult of
                  -- explicit return
                  EdhReturn !rtnVal -> rtnVal
                  -- no explicit return
                  !mthRtn -> mthRtn
    where
      !callerCtx = edh'context ets
      !new'stack = edh'ctx'tip callerCtx : edh'ctx'stack callerCtx

-- The Edh call convention is so called call-by-repacking, i.e. a new pack of
-- arguments are evaluated & packed at the calling site, then passed to the
-- callee site, where arguments in the pack are received into an entity to be
-- used as the run-scope of the callee, the receiving may include re-packing
-- into attributes manifested for rest-args. For any argument mentioned by
-- the callee but missing from the pack from the caller, the call should fail
-- if the callee did not specify a default expr for the missing arg; if the
-- callee did have a default expr specified, the default expr should be eval'ed
-- in the callee's lexial context to provide the missing value into the entity
-- with attr name of that arg.

-- This is semantically much the same as Python's call convention, regarding
-- positional and keyword argument matching, in addition with the following:
--  * wildcard receiver - receive all keyword arguments into the entity
--  * retargeting - don't receive the argument into the entity, but assign
--    to an attribute of another object, typically `this` object in scope
--  * argument renaming - match the name as sent, receive to a differently
--     named attribute of the entity. while renaming a positional argument
--     is doable but meaningless, you'd just use the later name for the arg
--  * rest-args repacking, in forms of:
--     *args
--     **kwargs
--     ***apk

recvEdhArgs ::
  EdhThreadState ->
  Context ->
  ArgsReceiver ->
  ArgsPack ->
  (KwArgs -> STM ()) ->
  STM ()
recvEdhArgs !etsCaller !recvCtx !argsRcvr apk@(ArgsPack !posArgs !kwArgs) !exit =
  case argsRcvr of
    PackReceiver argRcvrs _ ->
      iopdEmpty >>= \ !em ->
        let go :: [ArgReceiver] -> ArgsPack -> STM ()
            go [] !apk' =
              woResidual apk' $ iopdSnapshot em >>= edhDoSTM etsCaller . exit
            go (r : rest) !apk' =
              recvFromPack apk' em r $ \ !apk'' -> go rest apk''
         in go argRcvrs apk
    SingleReceiver argRcvr ->
      iopdEmpty >>= \ !em ->
        recvFromPack apk em argRcvr $ \ !apk' ->
          woResidual apk' $ iopdSnapshot em >>= edhDoSTM etsCaller . exit
    WildReceiver _ ->
      if null posArgs
        then edhDoSTM etsCaller $ exit kwArgs
        else
          throwEdh etsCaller EvalError $
            "unexpected "
              <> T.pack (show $ length posArgs)
              <> " positional argument(s) to wild receiver"
    NullaryReceiver ->
      if null posArgs
        then edhDoSTM etsCaller $ exit kwArgs
        else
          throwEdh etsCaller EvalError $
            "unexpected "
              <> T.pack (show $ length posArgs)
              <> " positional argument(s) to nullary receiver"
  where
    -- execution of the args receiving always in the callee's outer context
    !etsRecv = etsCaller {edh'context = recvCtx}

    recvFromPack ::
      ArgsPack ->
      IOPD AttrKey EdhValue ->
      ArgReceiver ->
      (ArgsPack -> STM ()) ->
      STM ()
    recvFromPack pk@(ArgsPack !posArgs' !kwArgs') !em !argRcvr !exit' =
      case argRcvr of
        RecvRestPosArgs (AttrAddrSrc (NamedAttr "_") _) _ ->
          -- silently drop the value to single underscore, while consume the args
          -- from incoming pack
          exit' (ArgsPack [] kwArgs')
        RecvRestPosArgs (AttrAddrSrc !argAddr _) _ ->
          resolveEdhAttrAddr etsRecv argAddr $ \ !argKey -> do
            iopdInsert argKey (EdhArgsPack $ ArgsPack posArgs' odEmpty) em
            exit' (ArgsPack [] kwArgs')
        RecvRestKwArgs (AttrAddrSrc (NamedAttr "_") _) _ ->
          -- silently drop the value to single underscore, while consume the args
          -- from incoming pack
          exit' (ArgsPack posArgs' odEmpty)
        RecvRestKwArgs (AttrAddrSrc !argAddr _) _ ->
          resolveEdhAttrAddr etsRecv argAddr $ \ !argKey -> do
            iopdInsert argKey (EdhArgsPack $ ArgsPack [] kwArgs') em
            exit' (ArgsPack posArgs' odEmpty)
        RecvRestPkArgs (AttrAddrSrc (NamedAttr "_") _) _ ->
          -- silently drop the value to single underscore, while consume the args
          -- from incoming pack
          exit' (ArgsPack [] odEmpty)
        RecvRestPkArgs (AttrAddrSrc !argAddr _) _ ->
          resolveEdhAttrAddr etsRecv argAddr $ \ !argKey -> do
            iopdInsert argKey (EdhArgsPack pk) em
            exit' (ArgsPack [] odEmpty)
        RecvArg (AttrAddrSrc (NamedAttr "_") _) _ _ _ ->
          -- silently drop the value to single underscore, while consume the arg
          -- from incoming pack
          resolveArgValue (AttrByName "_") Nothing $
            \(_, posArgs'', kwArgs'') -> exit' (ArgsPack posArgs'' kwArgs'')
        RecvArg (AttrAddrSrc !argAddr _) _anno !argTgtAddr !argDefault ->
          resolveEdhAttrAddr etsRecv argAddr $ \ !argKey ->
            resolveArgValue argKey argDefault $
              \(!argVal, !posArgs'', !kwArgs'') -> case argTgtAddr of
                Nothing -> do
                  iopdInsert argKey argVal em
                  exit' (ArgsPack posArgs'' kwArgs'')
                Just (DirectRef (AttrAddrSrc !addr _)) -> case addr of
                  NamedAttr "_" ->
                    -- drop
                    exit' (ArgsPack posArgs'' kwArgs'')
                  NamedAttr !attrName -> do
                    -- simple rename
                    iopdInsert (AttrByName attrName) argVal em
                    exit' (ArgsPack posArgs'' kwArgs'')
                  QuaintAttr !attrName -> do
                    -- odd rename
                    iopdInsert (AttrByName attrName) argVal em
                    exit' (ArgsPack posArgs'' kwArgs'')
                  SymbolicAttr !symName ->
                    -- todo support this ?
                    throwEdh etsCaller UsageError $
                      "do you mean `this.@" <> symName <> "` instead ?"
                  IntplSymAttr !src _x ->
                    -- todo support this ?
                    throwEdh etsCaller UsageError $
                      "do you mean `this.@( " <> src <> " )` instead ?"
                  LitSymAttr !sym -> do
                    iopdInsert (AttrBySym sym) argVal em
                    exit' (ArgsPack posArgs'' kwArgs'')
                  MissedAttrName ->
                    throwEdh
                      etsCaller
                      EvalError
                      "incomplete syntax: missing attribute name"
                  MissedAttrSymbol ->
                    throwEdh
                      etsCaller
                      EvalError
                      "incomplete syntax: missing symbolic attribute name"
                Just addr@IndirectRef {} ->
                  -- do assignment in callee's context,
                  -- and return to caller's afterwards
                  runEdhTx etsRecv $
                    assignEdhTarget (AttrExpr addr) argVal $
                      \_assignResult _ets -> exit' (ArgsPack posArgs'' kwArgs'')
                !tgt ->
                  throwEdh etsCaller UsageError $
                    "invalid argument retarget: "
                      <> T.pack (show tgt)
      where
        resolveArgValue ::
          AttrKey ->
          Maybe ExprSrc ->
          ((EdhValue, [EdhValue], KwArgs) -> STM ()) ->
          STM ()
        resolveArgValue !argKey !argDefault !exit'' = do
          let (inKwArgs, kwArgs'') = odTakeOut argKey kwArgs'
          case inKwArgs of
            Just argVal -> exit'' (argVal, posArgs', kwArgs'')
            _ -> case posArgs' of
              (posArg : posArgs'') -> exit'' (posArg, posArgs'', kwArgs'')
              [] -> case argDefault of
                -- always eval the default value atomically in callee's context
                Just (ExprSrc !defaultExpr _) ->
                  runEdhTx etsRecv $
                    evalExpr' defaultExpr NoDocCmt $ \ !val _ets ->
                      exit'' (edhDeFlowCtrl val, posArgs', kwArgs'')
                _ ->
                  throwEdh etsCaller UsageError $
                    "missing argument: "
                      <> attrKeyStr argKey
    woResidual :: ArgsPack -> STM () -> STM ()
    woResidual (ArgsPack !posResidual !kwResidual) !exit'
      | not (null posResidual) =
        throwEdh etsCaller UsageError $
          "extraneous "
            <> T.pack (show $ length posResidual)
            <> " positional argument(s)"
      | not (odNull kwResidual) =
        throwEdh etsCaller UsageError $
          "extraneous keyword arguments: "
            <> T.pack
              (unwords (show <$> odKeys kwResidual))
      | otherwise =
        exit'

-- | Pack args as expressions, normally in preparation of calling another
-- interpreter procedure
packEdhExprs :: EdhThreadState -> [ArgSender] -> (ArgsPack -> STM ()) -> STM ()
packEdhExprs !ets !pkrs !pkExit = do
  kwIOPD <- iopdEmpty
  let pkExprs :: [ArgSender] -> ([EdhValue] -> STM ()) -> STM ()
      pkExprs [] !exit = exit []
      pkExprs (x : xs) !exit = case x of
        UnpackPosArgs _ ->
          throwEdh ets EvalError "unpack to expr not supported yet"
        UnpackKwArgs _ ->
          throwEdh ets EvalError "unpack to expr not supported yet"
        UnpackPkArgs _ ->
          throwEdh ets EvalError "unpack to expr not supported yet"
        SendPosArg (ExprSrc !argExpr !arg'span) -> pkExprs xs $
          \ !posArgs -> do
            !xu <- newRUID'STM
            exit $
              EdhExpr (ExprDefi xu argExpr curSrcLoc {src'range = arg'span}) "" :
              posArgs
        SendKwArg (AttrAddrSrc !kwAddr _) (ExprSrc !argExpr !arg'span) ->
          resolveEdhAttrAddr ets kwAddr $ \ !kwKey -> do
            !xu <- newRUID'STM
            iopdInsert
              kwKey
              ( EdhExpr
                  (ExprDefi xu argExpr curSrcLoc {src'range = arg'span})
                  ""
              )
              kwIOPD
            pkExprs xs $ \ !posArgs' -> exit posArgs'
  pkExprs pkrs $ \ !args ->
    iopdSnapshot kwIOPD >>= \ !kwargs -> pkExit $ ArgsPack args kwargs
  where
    curSrcLoc = edh'exe'src'loc $ edh'ctx'tip $ edh'context ets

-- | Pack args as caller, normally in preparation of calling another procedure
packEdhArgs :: EdhThreadState -> [ArgSender] -> (ArgsPack -> STM ()) -> STM ()
packEdhArgs !ets !argSenders !pkExit = do
  !kwIOPD <- iopdEmpty
  let pkArgs :: [ArgSender] -> ([EdhValue] -> STM ()) -> STM ()
      pkArgs [] !exit = exit []
      pkArgs (x : xs) !exit = do
        let unpackDict :: DictStore -> STM ()
            unpackDict !ds = do
              !dkvl <- iopdToList ds
              dictKvs2Kwl dkvl $ \ !kvl -> do
                iopdUpdate kvl kwIOPD
                pkArgs xs exit
            unpackObj :: EntityStore -> STM ()
            unpackObj !es =
              iopdLookup (AttrByName edhExportsMagicName) es >>= \case
                Just (EdhObject !expWrapper) ->
                  case edh'obj'store expWrapper of
                    HashStore !esExpFrom ->
                      flip iopdUpdate kwIOPD =<< iopdToList esExpFrom
                    -- todo warn or err out in case of bad export wrapper
                    _ -> pkArgs xs exit
                _ -> pkArgs xs exit
            edhVal2Kw :: EdhValue -> STM () -> (AttrKey -> STM ()) -> STM ()
            edhVal2Kw !k !nopExit !exit' = case k of
              EdhString !name -> exit' $ AttrByName name
              EdhSymbol !sym -> exit' $ AttrBySym sym
              _ -> nopExit
            dictKvs2Kwl ::
              [(EdhValue, EdhValue)] ->
              ([(AttrKey, EdhValue)] -> STM ()) ->
              STM ()
            dictKvs2Kwl !ps !exit' = go ps []
              where
                go :: [(EdhValue, EdhValue)] -> [(AttrKey, EdhValue)] -> STM ()
                go [] !kvl = exit' kvl
                go ((k, v) : rest) !kvl =
                  edhVal2Kw k (go rest kvl) $ \ !k' -> go rest ((k', v) : kvl)
        case x of
          UnpackPosArgs !posExpr ->
            runEdhTx etsPacking $
              evalExprSrc posExpr $ \ !val _ets -> do
                let na = edhValueDesc ets val $ \ !badValDesc ->
                      throwEdh ets EvalError $
                        "can not unpack args from a " <> badValDesc
                case edhUltimate val of
                  (EdhArgsPack (ArgsPack !posArgs _kwArgs)) ->
                    pkArgs xs $ \ !posArgs' -> exit (posArgs ++ posArgs')
                  (EdhList (List _ !l)) -> pkArgs xs $ \ !posArgs -> do
                    ll <- readTVar l
                    exit ((edhNonNil <$> ll) ++ posArgs)
                  EdhObject !obj -> case edh'obj'store obj of
                    HostStore hs -> case unwrapHostValue hs of
                      -- a data class instance
                      -- syntactic sugar - 1 star unpacking of data instance
                      -- data fields to be unpacked as kwargs
                      Just (ArgsPack [_cls] !dataFields) -> do
                        iopdUpdate (odToList dataFields) kwIOPD
                        pkArgs xs $ \ !posArgs' -> exit posArgs'
                      _ -> na
                    _ -> na
                  _ -> na
          UnpackKwArgs !kwExpr ->
            runEdhTx etsPacking $
              evalExprSrc kwExpr $ \ !val _ets ->
                case edhUltimate val of
                  EdhArgsPack (ArgsPack _posArgs !kwArgs') -> do
                    iopdUpdate (odToList kwArgs') kwIOPD
                    pkArgs xs $ \ !posArgs' -> exit posArgs'
                  EdhPair !k !v ->
                    edhVal2Kw
                      k
                      ( throwEdh ets UsageError $
                          "invalid keyword type: " <> edhTypeNameOf k
                      )
                      $ \ !kw -> do
                        iopdInsert kw (edhNonNil $ edhDeFlowCtrl v) kwIOPD
                        pkArgs xs exit
                  EdhDict (Dict !ds) -> unpackDict ds
                  EdhObject !obj -> case edh'obj'store obj of
                    HashStore !hs -> unpackObj hs
                    ClassStore !cls -> unpackObj (edh'class'arts cls)
                    HostStore {} -> edhValueRepr ets val $ \ !objRepr ->
                      throwEdh ets EvalError $
                        "can not unpack kwargs from a host object - "
                          <> objRepr
                  _ -> edhValueDesc ets val $ \ !badValDesc ->
                    throwEdh ets EvalError $
                      "can not unpack kwargs from a "
                        <> badValDesc
          UnpackPkArgs !pkExpr ->
            runEdhTx etsPacking $
              evalExprSrc pkExpr $ \ !val _ets ->
                case edhUltimate val of
                  (EdhArgsPack (ArgsPack !posArgs !kwArgs')) -> do
                    iopdUpdate (odToList kwArgs') kwIOPD
                    pkArgs xs $ \ !posArgs' -> exit (posArgs ++ posArgs')
                  _ -> edhValueDesc ets val $ \ !badValDesc ->
                    throwEdh ets EvalError $
                      "can not unpack apk from a "
                        <> badValDesc
          SendPosArg !argExpr ->
            runEdhTx etsPacking $
              evalExprSrc argExpr $ \ !val _ets -> pkArgs xs $
                \ !posArgs -> exit (edhNonNil (edhDeFlowCtrl val) : posArgs)
          SendKwArg (AttrAddrSrc !kwAddr _) !argExpr ->
            runEdhTx etsPacking $
              evalExprSrc argExpr $ \ !val _ets ->
                case kwAddr of
                  NamedAttr "_" ->
                    -- silently drop the value to keyword of single
                    -- underscore, the user may just want its side-effect
                    pkArgs xs exit
                  _ -> resolveEdhAttrAddr ets kwAddr $ \ !kwKey -> do
                    iopdInsert kwKey (edhDeFlowCtrl val) kwIOPD
                    pkArgs xs exit
  pkArgs argSenders $ \ !posArgs -> do
    !kwArgs <- iopdSnapshot kwIOPD
    -- restore original tx state after args packed
    pkExit $ ArgsPack posArgs kwArgs
  where
    !ctx = edh'context ets
    !tip = edh'ctx'tip ctx
    !etsPacking =
      ets
        { edh'context =
            ctx
              { -- stack the tip frame one more time up, so effectful artifacts
                -- directly in caller's scope are available during args packing
                edh'ctx'tip = tip,
                edh'ctx'stack = tip : edh'ctx'stack ctx,
                -- discourage artifact definition during args packing
                edh'ctx'pure = True
              }
        }

callMagicMethod ::
  Object ->
  AttrKey ->
  ArgsPack ->
  EdhTxExit EdhValue ->
  EdhTx
callMagicMethod !obj !magicKey !apk !exit =
  invokeMagic obj magicKey apk exit ($)

invokeMagic ::
  Object ->
  AttrKey ->
  ArgsPack ->
  EdhTxExit EdhValue ->
  (((Object, EdhValue) -> STM ()) -> (Object, EdhValue) -> STM ()) ->
  EdhTx
invokeMagic !obj !magicKey !apk !exit !checkBypassCall !ets =
  case edh'obj'store obj of
    -- a class object can only get magic from its/the meta class,
    -- magics provided by a class is for its instances, not itself
    ClassStore {} ->
      lookupEdhObjAttr (edh'obj'class obj) magicKey
        >>= checkBypassCall callAsMethod
    _ ->
      runEdhTx ets $
        getObjAttrWithMagic'
          obj
          magicKey
          (\_ets -> checkBypassCall callAsMethod (obj, EdhNil))
          (\result _ets -> checkBypassCall callAsMethod result)
  where
    callAsMethod :: (Object, EdhValue) -> STM ()
    callAsMethod = \case
      (_, EdhBoundProc !callee !this !that !effOuter) ->
        callProc callee this that $
          flip (maybe id) effOuter $
            \ !outerStack !s -> s {edh'effects'stack = outerStack}
      (this, EdhProcedure !callee !effOuter) -> callProc
        callee
        this
        obj
        $ flip (maybe id) effOuter $
          \ !outerStack !s -> s {edh'effects'stack = outerStack}
      (badInst, EdhNil) -> edhObjRepr ets obj $ \ !objRepr ->
        throwEdh ets UsageError $
          "no " <> attrKeyStr magicKey <> " magic on "
            <> objClassName obj
            <> "("
            <> objClassName badInst
            <> ") object: "
            <> objRepr
      (badInst, badMagic) -> edhSimpleDesc ets badMagic $ \ !badDesc ->
        edhObjRepr ets obj $ \ !objRepr ->
          throwEdh ets UsageError $
            "bad " <> attrKeyStr magicKey <> " magic " <> badDesc
              <> " on "
              <> objClassName obj
              <> "("
              <> objClassName badInst
              <> ") object: "
              <> objRepr

    callerScope = contextScope $ edh'context ets

    callProc :: EdhProcDefi -> Object -> Object -> (Scope -> Scope) -> STM ()
    callProc !callee !this !that !scopeMod = case callee of
      -- calling a method procedure
      EdhMethod !mth ->
        runEdhTx ets $ callEdhMethod this that mth apk scopeMod exit
      -- calling an interpreter procedure
      EdhIntrpr !mth -> case edh'procedure'decl mth of
        HostDecl {} -> do
          -- a host interpreter proc runs in its caller's lexical context,
          -- in addition to sharing of the scope entity with the caller,
          -- which is implemented in `callEdhMethod`
          let scopeMod' s =
                scopeMod $ s {edh'scope'proc = edh'scope'proc callerScope}
          runEdhTx ets $ callEdhMethod this that mth apk scopeMod' exit
        ProcDecl {} -> do
          -- an Edh interpreter proc needs a `callerScope` as its 1st arg
          let callerCtx = edh'context ets
              ArgsPack args kwargs = apk
          !argCallerScope <- mkScopeWrapper ets $ contextScope callerCtx
          let apk' = ArgsPack (EdhObject argCallerScope : args) kwargs
          runEdhTx ets $ callEdhMethod this that mth apk' scopeMod exit
      --
      _ ->
        throwEdh ets UsageError $
          "such magic method not supported yet: " <> T.pack (show callee)

-- | Make a synchronous call to the specified procedure
--
-- NOTE use @LitExpr@ with @ValueLiteral@ in case you need to pass evaluated
--      values as arguments
edhMakeCall :: EdhValue -> [ArgSender] -> EdhTxExit EdhValue -> EdhTx
edhMakeCall !calleeVal !aSndrs !exit !ets =
  edhPrepareCall ets calleeVal aSndrs $ \ !mkCall -> runEdhTx ets $ mkCall exit

-- | Make a synchronous call to the specified procedure
--
-- NOTE mind to provide expression values as in the apk, in case the callee is
--      an interpreter procedure
edhMakeCall' :: EdhValue -> ArgsPack -> EdhTxExit EdhValue -> EdhTx
edhMakeCall' !calleeVal !apk !exit !ets =
  edhPrepareCall' ets calleeVal (const ($ apk)) $
    \ !mkCall -> runEdhTx ets $ mkCall exit

-- Each Edh call is carried out in 2 phases, the preparation and the actual
-- call execution. This is necessary to support the `go/defer` mechanism,
-- where the preparation and call execution happen in different contexts.
--
-- - In case of `go`, the preparation happens in the forker thread, while the
--   actual call is executed in the forked descendant thread
--
-- - In case of `defer`, the preparation happens when it's scheduled, while
--   the actual call is executed when then thread is about to terminate
--
-- - The call is executed subsequently in the same thread, immediately after
--   it's prepared in other cases

-- | Prepare an Edh call
edhPrepareCall ::
  EdhThreadState -> -- ets to prepare the call
  EdhValue -> -- callee value
  [ArgSender] -> -- specification for the arguments pack
  -- callback to receive the prepared call
  ((EdhTxExit EdhValue -> EdhTx) -> STM ()) ->
  STM ()
edhPrepareCall !etsCallPrep !calleeVal !argsSndr !callMaker =
  edhPrepareCall' etsCallPrep calleeVal apkr callMaker
  where
    apkr :: EdhValue -> (ArgsPack -> STM ()) -> STM ()
    apkr !realCallee = case realCallee of
      EdhProcedure EdhIntrpr {} _ -> packEdhExprs etsCallPrep argsSndr
      EdhBoundProc EdhIntrpr {} _ _ _ -> packEdhExprs etsCallPrep argsSndr
      EdhProcedure EdhIntrOp {} _ -> packEdhExprs etsCallPrep argsSndr
      EdhBoundProc EdhIntrOp {} _ _ _ -> packEdhExprs etsCallPrep argsSndr
      EdhProcedure (EdhOprtor _ _ _ !op'proc) _ ->
        if is3Args $ edh'procedure'args $ edh'procedure'decl op'proc
          then packEdhExprs etsCallPrep argsSndr
          else packEdhArgs etsCallPrep argsSndr
      EdhBoundProc (EdhOprtor _ _ _ !op'proc) _ _ _ ->
        if is3Args $ edh'procedure'args $ edh'procedure'decl op'proc
          then packEdhExprs etsCallPrep argsSndr
          else packEdhArgs etsCallPrep argsSndr
      _ -> packEdhArgs etsCallPrep argsSndr

    is3Args = \case
      PackReceiver [RecvArg {}, RecvArg {}, RecvArg {}] _ -> True
      _ -> False

-- | Prepare an Edh call
edhPrepareCall' ::
  EdhThreadState -> -- ets to prepare the call
  EdhValue -> -- callee value
  (EdhValue -> (ArgsPack -> STM ()) -> STM ()) -> -- args packer per real callee
  -- callback to receive the prepared call
  ((EdhTxExit EdhValue -> EdhTx) -> STM ()) ->
  STM ()
edhPrepareCall' !etsCallPrep !calleeVal !apkr !callMaker =
  case calleeVal of
    EdhBoundProc !callee !this !that !effOuter ->
      apkr calleeVal $ \apk ->
        callProc apk callee this that $
          flip (maybe id) effOuter $
            \ !outerStack !s -> s {edh'effects'stack = outerStack}
    EdhProcedure !callee !effOuter ->
      apkr calleeVal $ \apk ->
        callProc
          apk
          callee
          (edh'scope'this callerScope)
          (edh'scope'that callerScope)
          $ flip (maybe id) effOuter $
            \ !outerStack !s -> s {edh'effects'stack = outerStack}
    (EdhObject !obj) -> case edh'obj'store obj of
      -- calling a class
      ClassStore {} ->
        apkr calleeVal $ \apk ->
          callMaker $ \ !exit -> edhConstructObj obj apk $
            \ !instObj !ets -> exitEdh ets exit $ EdhObject instObj
      -- calling an object
      _ ->
        lookupEdhObjAttr obj (AttrByName "__call__") >>= \case
          (!this', realCallee@(EdhProcedure !callee !effOuter)) ->
            apkr realCallee $ \apk ->
              callProc apk callee this' obj $
                flip (maybe id) effOuter $
                  \ !outerStack !s -> s {edh'effects'stack = outerStack}
          (_, realCallee@(EdhBoundProc !callee !this !that !effOuter)) ->
            apkr realCallee $ \apk ->
              callProc apk callee this that $
                flip (maybe id) effOuter $
                  \ !outerStack !s -> s {edh'effects'stack = outerStack}
          _ -> edhSimpleDesc etsCallPrep calleeVal $ \ !badDesc ->
            throwEdh etsCallPrep EvalError $
              "no __call__ method on " <> badDesc
    _ -> edhValueRepr etsCallPrep calleeVal $ \ !calleeRepr ->
      throwEdh etsCallPrep EvalError $
        "can not call a " <> edhTypeNameOf calleeVal <> ": " <> calleeRepr
  where
    callerScope = contextScope $ edh'context etsCallPrep

    callProc ::
      ArgsPack -> EdhProcDefi -> Object -> Object -> (Scope -> Scope) -> STM ()
    callProc apk@(ArgsPack !args !kwargs) !callee !this !that !scopeMod =
      case callee of
        -- calling a method procedure
        EdhMethod !mth ->
          callMaker $ \ !exit -> callEdhMethod this that mth apk scopeMod exit
        --

        -- calling an interpreter procedure
        EdhIntrpr !mth -> do
          case edh'procedure'decl mth of
            HostDecl {} -> do
              -- a host interpreter proc runs in its caller's lexical context,
              -- in addition to sharing of the scope entity with the caller,
              -- which is implemented in `callEdhMethod`
              let scopeMod' s =
                    scopeMod $ s {edh'scope'proc = edh'scope'proc callerScope}
              callMaker $ \ !exit ->
                callEdhMethod this that mth apk scopeMod' exit
            ProcDecl {} -> do
              -- an Edh interpreter proc needs a `callerScope` as its 1st arg
              let callerCtx = edh'context etsCallPrep
              !argCallerScope <-
                mkScopeWrapper etsCallPrep $ contextScope callerCtx
              let apk' = ArgsPack (EdhObject argCallerScope : args) kwargs
              callMaker $ \ !exit ->
                callEdhMethod this that mth apk' scopeMod exit
        --

        -- calling a producer procedure
        EdhPrducr !mth -> case edh'procedure'decl mth of
          HostDecl {} ->
            throwEdh etsCallPrep EvalError "bug: host producer procedure"
          ProcDecl _ _ _ !pb !pl ->
            case edhUltimate <$> odLookup (AttrByName "outlet") kwargs of
              Nothing -> do
                outlet <- newSink
                callMaker $ \ !exit ->
                  launchEventProducer (exit . EdhSink) outlet $
                    callEdhMethod'
                      Nothing
                      this
                      that
                      mth
                      pl
                      pb
                      ( ArgsPack args $
                          odFromList $
                            odToList kwargs
                              ++ [(AttrByName "outlet", EdhSink outlet)]
                      )
                      scopeMod
                      endOfEdh
              Just (EdhSink !outlet) -> callMaker $ \exit ->
                launchEventProducer (exit . EdhSink) outlet $
                  callEdhMethod'
                    Nothing
                    this
                    that
                    mth
                    pl
                    pb
                    (ArgsPack args kwargs)
                    scopeMod
                    endOfEdh
              Just !badVal ->
                throwEdh etsCallPrep UsageError $
                  "the value passed to a producer as `outlet` found to be a "
                    <> edhTypeNameOf badVal
        --

        -- calling a generator
        (EdhGnrtor _) ->
          throwEdh
            etsCallPrep
            EvalError
            "can only call a generator method by for-from-do loop"
        --

        -- calling an operator
        EdhIntrOp _fixity _op'prec !opDef -> case args of
          [EdhExpr (ExprDefi _ !lhx _) _, EdhExpr (ExprDefi _ !rhx _) _]
            | odNull kwargs -> callMaker $ \ !exit ->
              intrinsic'op
                opDef
                (ExprSrc lhx noSrcRange)
                (ExprSrc rhx noSrcRange)
                exit
          -- todo support kwargs?
          _ ->
            throwEdh
              etsCallPrep
              UsageError
              "an intrinsic operator can only be called with 2 positional args"
        EdhOprtor _ _ !op'pred !op'proc -> case args of
          [EdhExpr (ExprDefi _ !lhx _) _, EdhExpr (ExprDefi _ !rhx _) _]
            | odNull kwargs ->
              case edh'procedure'args $ edh'procedure'decl op'proc of
                (PackReceiver [RecvArg {}, RecvArg {}] _) ->
                  callMaker $ \ !exit ->
                    evalExpr lhx $ \ !lhVal ->
                      evalExpr rhx $ \ !rhVal ->
                        callEdhOperator
                          this
                          that
                          op'proc
                          op'pred
                          [edhDeCaseClose lhVal, edhDeCaseClose rhVal]
                          exit
                (PackReceiver [RecvArg {}, RecvArg {}, RecvArg {}] _) ->
                  callMaker $ \ !exit !etsCaller -> do
                    !scopeWrapper <-
                      mkScopeWrapper etsCaller $
                        contextScope $ edh'context etsCaller
                    runEdhTx etsCaller $
                      callEdhOperator
                        this
                        that
                        op'proc
                        op'pred
                        (EdhObject scopeWrapper : args)
                        exit
                _ ->
                  throwEdh etsCallPrep UsageError $
                    "invalid operator signature: "
                      <> T.pack
                        (show $ edh'procedure'args $ edh'procedure'decl op'proc)
          -- todo support kwargs?
          _ ->
            throwEdh
              etsCallPrep
              UsageError
              "an intrinsic operator can only be called with 2 positional args"
        --

        _ ->
          throwEdh etsCallPrep EvalError $
            "`edhPrepareCall` can not be used to call a "
              <> T.pack (show callee)

callEdhMethod ::
  Object ->
  Object ->
  ProcDefi ->
  ArgsPack ->
  (Scope -> Scope) ->
  EdhTxExit EdhValue ->
  EdhTx
callEdhMethod !this !that !mth !apk !scopeMod !exit =
  case edh'procedure'decl mth of
    -- calling a host method procedure
    HostDecl !hp -> \ !etsCaller -> do
      let !callerCtx = edh'context etsCaller
          !callerFrame = edh'ctx'tip callerCtx
          !callerScope = contextScope callerCtx
          -- a host procedure views the same scope entity as of the caller's
          -- call frame
          !mthScope =
            scopeMod
              Scope
                { edh'scope'entity = edh'scope'entity callerScope,
                  edh'scope'this = this,
                  edh'scope'that = that,
                  edh'scope'proc = mth,
                  edh'effects'stack = []
                }
      !calleeFrame <- newCallFrame mthScope $ edh'exe'src'loc callerFrame
      let !mthCtx =
            callerCtx
              { edh'ctx'tip = calleeFrame,
                edh'ctx'stack = callerFrame : edh'ctx'stack callerCtx,
                edh'ctx'genr'caller = Nothing,
                edh'ctx'match = true,
                edh'ctx'pure = False,
                edh'ctx'exp'target = Nothing,
                edh'ctx'eff'target = Nothing
              }
          !etsMth = etsCaller {edh'context = mthCtx}
      runEdhTx etsMth $
        hp apk $ \ !val ->
          -- return whatever the result a host procedure returned
          -- a host procedure is responsible for returning sense-making
          -- result anyway
          edhSwitchState etsCaller $ exit val
    -- calling an Edh method procedure
    ProcDecl _ _ _ !pb !pl ->
      callEdhMethod' Nothing this that mth pl pb apk scopeMod exit

callEdhMethod' ::
  Maybe EdhGenrCaller ->
  Object ->
  Object ->
  ProcDefi ->
  SrcLoc ->
  StmtSrc ->
  ArgsPack ->
  (Scope -> Scope) ->
  EdhTxExit EdhValue ->
  EdhTx
callEdhMethod'
  !gnr'caller
  !this
  !that
  !mth
  !proc'loc
  (StmtSrc !body'stmt _)
  !apk
  !scopeMod
  !exit
  !etsCaller = do
    !recvTipFrame <-
      newCallFrame
        (edh'procedure'lexi mth)
          { edh'scope'this = this,
            edh'scope'that = that
          }
        proc'loc
    let !recvCtx =
          callerCtx
            { edh'ctx'tip = recvTipFrame,
              edh'ctx'stack = new'stack,
              edh'ctx'genr'caller = Nothing,
              edh'ctx'match = true,
              edh'ctx'pure = False,
              edh'ctx'exp'target = Nothing,
              edh'ctx'eff'target = Nothing
            }
    recvEdhArgs
      etsCaller
      recvCtx
      (edh'procedure'args $ edh'procedure'decl mth)
      apk
      $ \ !ed -> do
        !esScope <- iopdFromList (odToList ed)
        let !mthScope =
              scopeMod
                Scope
                  { edh'scope'entity = esScope,
                    edh'scope'this = this,
                    edh'scope'that = that,
                    edh'scope'proc = mth,
                    edh'effects'stack = []
                  }
        !tipFrame <- newCallFrame mthScope proc'loc
        let !mthCtx =
              callerCtx
                { edh'ctx'tip = tipFrame,
                  edh'ctx'stack = new'stack,
                  edh'ctx'genr'caller = gnr'caller,
                  edh'ctx'match = true,
                  edh'ctx'pure = False,
                  edh'ctx'exp'target = Nothing,
                  edh'ctx'eff'target = Nothing
                }
            !etsMth = etsCaller {edh'context = mthCtx}
        runEdhTx etsMth $
          evalStmt body'stmt $ \ !bodyResult ->
            edhSwitchState etsCaller $
              exitEdhTx exit $ case edhDeFlowCtrl bodyResult of
                -- explicit return is sacred, the returner is assumed to have
                -- full responsibility/control over appropriate semantics
                EdhReturn !rtnVal -> rtnVal
                -- no explicit return
                !mthRtn -> mthRtn
    where
      !callerCtx = edh'context etsCaller
      !new'stack = edh'ctx'tip callerCtx : edh'ctx'stack callerCtx

edhPrepareForLoop ::
  EdhThreadState -> -- ets to prepare the looping
  Bool -> -- whether scoped loop
  ArgsReceiver ->
  ExprSrc ->
  StmtSrc ->
  (EdhValue -> STM ()) ->
  (EdhValue -> (EdhTxExit EdhValue -> EdhTx) -> STM ()) ->
  STM ()
edhPrepareForLoop
  !etsLoopPrep
  !scopedLoop
  !argsRcvr
  !iterExpr
  !bodyStmt
  !iterCollector
  !forLooper =
    case deParen1 iterExpr of -- a complex expression is better quoted within
    -- a pair of parenthesis; and we strip off only 1 layer of parenthesis
    -- here, so in case a pure context intended, double-parenthesis quoting
    -- will work e.g. an adhoc procedure defined then called, but that
    -- procedure would better not get defined into the enclosing scope, and it
    -- is preferably be named instead of being anonymous (with a single
    -- underscore in place of the procedure name in the definition).
      ExprSrc (CallExpr !calleeExpr (ArgsPacker !argsSndr _)) !iter'span ->
        -- loop over a procedure call
        runEdhTx etsLoopPrep $
          evalExprSrc calleeExpr $ \ !calleeVal _ets ->
            case calleeVal of
              EdhBoundProc callee@EdhGnrtor {} !this !that !effOuter ->
                loopCallGenr calleeVal iter'span argsSndr callee this that $
                  flip (maybe id) effOuter $
                    \ !outerStack !s -> s {edh'effects'stack = outerStack}
              EdhProcedure callee@EdhGnrtor {} !effOuter ->
                loopCallGenr
                  calleeVal
                  iter'span
                  argsSndr
                  callee
                  (edh'scope'this scopeLoopPrep)
                  (edh'scope'that scopeLoopPrep)
                  $ flip (maybe id) effOuter $
                    \ !outerStack !s -> s {edh'effects'stack = outerStack}
              (EdhObject !obj) ->
                -- calling an object
                lookupEdhObjAttr obj (AttrByName "__call__")
                  >>= \(!this', !mth) -> case mth of
                    EdhBoundProc callee@EdhGnrtor {} !this !that !effOuter ->
                      loopCallGenr mth iter'span argsSndr callee this that $
                        flip (maybe id) effOuter $
                          \ !outerStack !s -> s {edh'effects'stack = outerStack}
                    EdhProcedure callee@EdhGnrtor {} !effOuter ->
                      loopCallGenr mth iter'span argsSndr callee this' obj $
                        flip (maybe id) effOuter $
                          \ !outerStack !s -> s {edh'effects'stack = outerStack}
                    -- not a callable generator object, assume to loop over
                    -- its return value
                    _ -> edhPrepareCall etsLoopPrep calleeVal argsSndr $
                      \ !mkCall -> runEdhTx etsLoopPrep $
                        mkCall $ \ !iterVal _ets -> loopOverValue iterVal
              -- calling other procedures, assume to loop over its return value
              -- todo should producer procedures be specially handled here?
              --      the sink returned from it will assume sync producing
              --      semantics if this for-loop is prefixed with `go`, in this
              --      case both current thread and the producer procedure's
              --      thread are assumed event producers.
              _ ->
                runEdhTx etsLoopPrep $
                  evalExprSrc iterExpr $ \ !iterVal _ets ->
                    loopOverValue $ edhDeCaseWrap iterVal
      _ ->
        -- loop over an iterable value
        runEdhTx etsLoopPrep $
          evalExprSrc iterExpr $ \ !iterVal _ets ->
            loopOverValue $ edhDeCaseWrap iterVal
    where
      scopeLoopPrep = contextScope $ edh'context etsLoopPrep

      loopCallGenr ::
        EdhValue ->
        SrcRange ->
        [ArgSender] ->
        EdhProcDefi ->
        Object ->
        Object ->
        (Scope -> Scope) ->
        STM ()
      loopCallGenr
        !loopTgt
        !caller'span
        !argsSndr
        (EdhGnrtor !gnr'proc)
        !this
        !that
        !scopeMod =
          packEdhArgs etsLoopPrep argsSndr $ \ !apk ->
            case edh'procedure'decl gnr'proc of
              -- calling a host generator
              HostDecl !hp -> forLooper loopTgt $ \ !exit !etsLooper -> do
                -- a host procedure views the same scope entity as of the
                -- caller's call frame
                {- HLINT ignore "Reduce duplication" -}
                let !looperCtx = edh'context etsLooper
                    !looperFrame = edh'ctx'tip looperCtx
                    !callerFrame = frameMovePC looperFrame caller'span
                    !calleeScope =
                      Scope
                        { edh'scope'entity =
                            edh'scope'entity $
                              edh'frame'scope looperFrame,
                          edh'scope'this = this,
                          edh'scope'that = that,
                          edh'scope'proc = gnr'proc,
                          edh'effects'stack = []
                        }
                !calleeFrame <-
                  newCallFrame calleeScope $ edh'exe'src'loc callerFrame
                let !calleeCtx =
                      looperCtx
                        { edh'ctx'tip = calleeFrame,
                          edh'ctx'stack = callerFrame : edh'ctx'stack looperCtx,
                          edh'ctx'genr'caller = Just $ recvYield etsLooper exit,
                          edh'ctx'match = true,
                          edh'ctx'pure = False,
                          edh'ctx'exp'target = Nothing,
                          edh'ctx'eff'target = Nothing
                        }
                    !etsCallee = etsLooper {edh'context = calleeCtx}
                runEdhTx etsCallee $
                  hp apk $ \ !val ->
                    -- a host generator is responsible to return a sense-making
                    -- result anyway
                    edhSwitchState etsLooper $ exitEdhTx exit val

              -- calling an Edh generator
              ProcDecl _ _ _ !pb !pl ->
                forLooper loopTgt $ \ !exit !etsLooper -> do
                  let !looperCtx = edh'context etsLooper
                      !looperFrame = edh'ctx'tip looperCtx
                      !callerFrame = frameMovePC looperFrame caller'span
                      !etsCaller =
                        etsLooper
                          { edh'context =
                              looperCtx {edh'ctx'tip = callerFrame}
                          }
                  runEdhTx etsCaller $
                    callEdhMethod'
                      (Just $ recvYield etsLooper exit)
                      this
                      that
                      gnr'proc
                      pl
                      pb
                      apk
                      scopeMod
                      $ \ !gnrRtn ->
                        -- note it can be a return from unwrapped double-return
                        edhSwitchState etsLooper $ exitEdhTx exit gnrRtn
      loopCallGenr _ _ _ !callee _ _ _ =
        throwEdh etsLoopPrep EvalError $
          "bug: unexpected generator: " <> T.pack (show callee)

      -- receive one yielded value from the generator, the 'genrCont' here is
      -- to continue the generator execution, result passed to the 'genrCont'
      -- here is to be the eval'ed value of the `yield` expression from the
      -- generator's perspective, or exception to be thrown from there
      recvYield ::
        EdhThreadState ->
        EdhTxExit EdhValue ->
        EdhValue ->
        (Either (EdhThreadState, EdhValue) EdhValue -> STM ()) ->
        EdhTx
      recvYield !etsLooper !exit !yielded'val !genrCont !etsGenr = do
        let doOne !exitOne !etsTry =
              recvEdhArgs
                etsTry
                (edh'context etsTry)
                argsRcvr
                ( case yielded'val of
                    EdhArgsPack apk -> apk
                    _ -> ArgsPack [yielded'val] odEmpty
                )
                $ \ !em -> do
                  iopdUpdate (odToList em) $
                    edh'scope'entity $
                      edh'frame'scope $ edh'ctx'tip $ edh'context etsTry
                  runEdhTx etsTry $ evalStmtSrc bodyStmt exitOne
            doneOne !doResult = case edhDeCaseClose doResult of
              EdhContinue ->
                -- propagate explicit { continue } to generator
                genrCont $ Right EdhContinue
              EdhBreak ->
                -- break out of the for-from-do loop,
                -- the generator on <break> yielded should return {break},
                -- effectively have the for loop eval to nil
                genrCont $ Right EdhBreak
              EdhCaseOther ->
                -- send nil to generator on no-match of a branch
                genrCont $ Right nil
              EdhFallthrough ->
                -- send nil to generator on fallthrough
                genrCont $ Right nil
              EdhReturn EdhReturn {} ->
                -- this has special meaning
                -- Edh code should not use this pattern
                throwEdh
                  etsLooper
                  UsageError
                  "you don't double return from loop body"
              EdhReturn !rtnVal ->
                -- early return from for-from-do, the generator should
                -- propagate the double return as yield result to it,
                -- effectively have the for-from-do expression as a whole,
                -- eval to a return of the result
                genrCont $ Right $ EdhReturn $ EdhReturn rtnVal
              !val -> do
                -- vanilla val from do, send to generator
                iterCollector val
                genrCont $ Right val
        case yielded'val of
          EdhNil ->
            -- nil yielded from a generator effectively early stops
            exitEdh etsLooper exit nil
          EdhContinue ->
            throwEdh etsLooper EvalError "generator yielded continue"
          EdhBreak ->
            throwEdh etsLooper EvalError "generator yielded break"
          EdhReturn {} ->
            throwEdh etsLooper EvalError "generator yielded return"
          _ -> do
            !ctxDo <-
              if scopedLoop
                then do
                  !loopFrame <- newNestedFrame tipLooper
                  return
                    ctxLooper
                      { edh'ctx'tip = loopFrame,
                        -- push looper + generator call stack
                        edh'ctx'stack =
                          tipLooper :
                          edh'ctx'tip ctxGenr : edh'ctx'stack ctxGenr
                      }
                else
                  return
                    ctxLooper
                      { -- tip frame comes from the looper's ctx
                        -- push generator call stack
                        edh'ctx'stack =
                          edh'ctx'tip ctxGenr : edh'ctx'stack ctxGenr
                      }
            let !etsDo = etsGenr {edh'context = ctxDo}
            edhCatch etsDo doOne doneOne $
              \ !etsThrower !exv _recover rethrow ->
                case exv of
                  EdhNil -> rethrow nil -- no exception occurred in do block
                  _ ->
                    -- exception uncaught in do block
                    -- propagate to the generator, the genr may catch it or
                    -- the exception will propagate to outer of for-from-do
                    genrCont $ Left (etsThrower, exv)
        where
          ctxLooper = edh'context etsLooper
          tipLooper = edh'ctx'tip ctxLooper
          ctxGenr = edh'context etsGenr

      loopOverValue :: EdhValue -> STM ()
      loopOverValue !iterVal = forLooper ultIterVal $ \ !exit !etsLooper -> do
        let !ctxLooper = edh'context etsLooper
            tipLooper = edh'ctx'tip ctxLooper

            -- do one iteration
            do1 :: ArgsPack -> STM () -> STM ()
            do1 !apk !next = do
              !ctxDo <-
                if scopedLoop
                  then do
                    !loopFrame <- newNestedFrame tipLooper
                    return
                      ctxLooper
                        { edh'ctx'tip = loopFrame,
                          -- push looper call stack
                          edh'ctx'stack =
                            tipLooper : edh'ctx'stack ctxLooper
                        }
                  else return ctxLooper
              let !etsDo = etsLooper {edh'context = ctxDo}
              recvEdhArgs etsDo ctxDo argsRcvr apk $ \ !em -> do
                iopdUpdate (odToList em) $
                  edh'scope'entity $ edh'frame'scope $ edh'ctx'tip ctxDo
                runEdhTx etsDo $
                  evalStmtSrc bodyStmt $ \ !doResult _etsDone ->
                    case edhDeCaseClose doResult of
                      EdhBreak ->
                        -- break for loop
                        exitEdh etsLooper exit nil
                      EdhReturn EdhReturn {} ->
                        -- this has special meaning
                        -- Edh code should not use this pattern
                        throwEdh
                          etsLooper
                          UsageError
                          "you don't double return from loop body"
                      rtn@EdhReturn {} ->
                        -- early return during for loop
                        exitEdh etsLooper exit rtn
                      EdhContinue ->
                        -- explicit continue w/o yielding
                        next
                      EdhCaseOther ->
                        -- no-match, continue w/o yielding
                        next
                      EdhFallthrough ->
                        -- match but no result, continue w/o yielding
                        next
                      _ -> do
                        -- continue w/ yielding
                        iterCollector doResult
                        next

            -- loop over a series of args packs
            iterThem :: [ArgsPack] -> STM ()
            iterThem [] = exitEdh etsLooper exit nil
            iterThem (apk : apks) = do1 apk $ iterThem apks

            -- loop over a subscriber's channel of an event sink
            iterEvt :: TChan EdhValue -> STM ()
            iterEvt !subChan =
              edhDoSTM etsLooper $
                readTChan subChan >>= \case
                  EdhNil ->
                    -- nil marks end-of-stream from an event sink
                    exitEdh etsLooper exit nil -- stop the for-from-do loop
                  EdhArgsPack !apk -> do1 apk $ iterEvt subChan
                  !v -> do1 (ArgsPack [v] odEmpty) $ iterEvt subChan

        case ultIterVal of
          -- loop from an event sink
          (EdhSink !sink) ->
            subscribeEvents sink >>= \case
              Nothing -> exitEdh etsLooper exit nil -- already at eos
              Just (!subChan, !mrv) -> case mrv of
                Nothing -> iterEvt subChan
                Just !ev -> case ev of
                  EdhArgsPack !apk -> do1 apk $ iterEvt subChan
                  !v -> do1 (ArgsPack [v] odEmpty) $ iterEvt subChan
          -- loop from a positonal-only args pack
          (EdhArgsPack (ArgsPack !args !kwargs))
            | odNull kwargs ->
              iterThem
                [ case val of
                    EdhArgsPack !apk' -> apk'
                    _ -> ArgsPack [val] odEmpty
                  | val <- args
                ]
          -- loop from a keyword-only args pack
          (EdhArgsPack (ArgsPack !args !kwargs))
            | null args ->
              iterThem
                [ ArgsPack [attrKeyValue k, v] odEmpty
                  | (k, v) <- odToList kwargs
                ]
          -- loop from a list
          (EdhList (List _ !l)) -> do
            !ll <- readTVar l
            iterThem
              [ case val of
                  EdhArgsPack !apk' -> apk'
                  _ -> ArgsPack [val] odEmpty
                | val <- ll
              ]

          -- loop from a dict
          (EdhDict (Dict !d)) -> do
            !del <- iopdToList d
            -- don't be tempted to yield pairs from a dict here,
            -- it'll be messy if some entry values are themselves pairs
            iterThem [ArgsPack [k, v] odEmpty | (k, v) <- del]

          -- TODO define the magic method for an object to be able to respond
          --      to for-from-do looping

          _ -> parseEdhIndex etsLooper ultIterVal $ \case
            Right (EdhSlice (Just !start) (Just !stop) !step) -> do
              let !stepN = fromMaybe (if stop >= start then 1 else -1) step
                  iterRange :: Int -> STM ()
                  iterRange !i =
                    do1 (ArgsPack [EdhDecimal $ fromIntegral i] odEmpty) $ do
                      let i' = i + stepN
                      if stepN > 0
                        then
                          if i' >= stop
                            then exitEdh etsLooper exit nil
                            else iterRange i'
                        else
                          if i' <= stop
                            then exitEdh etsLooper exit nil
                            else iterRange i'
              iterRange start
            _ -> edhSimpleDesc etsLooper iterVal $ \ !badDesc ->
              throwEdh etsLooper EvalError $
                "can not do a for loop from " <> badDesc
        where
          !ultIterVal = edhUltimate iterVal

-- todo this should really be in `CoreLang.hs`, but there has no access to
--      'throwEdh' without cyclic imports, maybe some day we shall try
--      `.hs-boot` files

-- | resolve an attribute addressor, either alphanumeric named or symbolic
resolveEdhAttrAddr ::
  EdhThreadState -> AttrAddr -> (AttrKey -> STM ()) -> STM ()
resolveEdhAttrAddr _ (NamedAttr !attrName) !exit = exit (AttrByName attrName)
resolveEdhAttrAddr _ (QuaintAttr !attrName) !exit = exit (AttrByName attrName)
resolveEdhAttrAddr !ets (SymbolicAttr !symName) !exit =
  let scope = contextScope $ edh'context ets
   in resolveEdhCtxAttr scope (AttrByName symName) >>= \case
        Just (!val, _) -> case val of
          (EdhSymbol !symVal) -> exit (AttrBySym symVal)
          (EdhString !nameVal) -> exit (AttrByName nameVal)
          _ ->
            throwEdh ets EvalError $
              "not a symbol/string as "
                <> symName
                <> ", it is a "
                <> edhTypeNameOf val
                <> ": "
                <> T.pack (show val)
        Nothing ->
          throwEdh ets EvalError $
            "no symbol/string named "
              <> T.pack (show symName)
              <> " available"
resolveEdhAttrAddr !ets (IntplSymAttr src !x) !exit = runEdhTx ets $
  evalExprSrc x $
    \ !symVal _ets -> case edhUltimate symVal of
      EdhSymbol !sym -> exit $ AttrBySym sym
      EdhString !nm -> exit $ AttrByName nm
      _ -> edhSimpleDesc ets symVal $ \ !badDesc ->
        throwEdh ets UsageError $
          "symbol interpolation given unexpected value: "
            <> badDesc
            <> "\n 🔣  evaluated from @( "
            <> src
            <> " )"
resolveEdhAttrAddr _ (LitSymAttr !sym) !exit = exit $ AttrBySym sym
resolveEdhAttrAddr !ets MissedAttrName _exit =
  throwEdh
    ets
    EvalError
    "incomplete syntax: missing attribute name"
resolveEdhAttrAddr !ets MissedAttrSymbol _exit =
  throwEdh
    ets
    EvalError
    "incomplete syntax: missing symbolic attribute name"
{-# INLINE resolveEdhAttrAddr #-}

-- | Yield from a host generator procedure
edhYield :: EdhValue -> EdhTxExit EdhValue -> EdhTxExit EdhValue -> EdhTx
edhYield !val !next'iter !genr'exit !ets = case edh'ctx'genr'caller ctx of
  Nothing ->
    throwEdh ets EvalError "yield from a procedure not called as generator"
  Just iter'cb -> runEdhTx ets $
    iter'cb val $ \case
      Left (!etsThrower, !exv) ->
        -- note we can actually be encountering the exception
        -- occurred from a descendant thread forked by the thread
        -- running the enclosing generator, @etsThrower@ has the
        -- correct task queue, and @ets@ has the correct contextual
        -- callstack anyway
        edhThrow etsThrower {edh'context = edh'context ets} exv
      Right EdhBreak ->
        -- usually `break` stmt from the calling for-loop,
        -- return nil from the generator, so the loop ends with nil
        exitEdh ets genr'exit nil
      Right (EdhReturn !rtn) ->
        -- usually `return` stmt from the calling for-loop,
        -- propagate the value to return as however the generator returns,
        -- it can be a sacred double-return, in which case the for-loop will
        -- evaluate to a `return` value, thus actually early return from the
        -- outer-loop procedure
        exitEdh ets genr'exit rtn
      Right !yieldGot ->
        -- usually some value evaluated from the body of the calling for-loop,
        -- proceed to next iteration
        exitEdh ets next'iter yieldGot
  where
    !ctx = edh'context ets

-- | Throw a tagged error from Edh computation
--
-- a bit similar to `return` in Haskell, this doesn't cease the execution
-- of subsequent actions following it, be cautious.
throwEdhTx :: EdhErrorTag -> Text -> EdhTx
throwEdhTx !et !msg !ets = throwEdh ets et msg
{-# INLINE throwEdhTx #-}

-- | Throw a tagged error from STM monad running Edh computation
--
-- a bit similar to `return` in Haskell, this doesn't cease the execution
-- of subsequent actions following it, be cautious.
throwEdh :: EdhThreadState -> EdhErrorTag -> Text -> STM a
throwEdh !ets !tag !msg = throwEdh' ets tag msg []
{-# INLINE throwEdh #-}

-- | Throw a tagged error with some detailed data, from STM monad running Edh
-- computation
--
-- a bit similar to `return` in Haskell, this doesn't cease the execution
-- of subsequent actions following it, be cautious.
throwEdh' ::
  EdhThreadState -> EdhErrorTag -> Text -> [(AttrKey, EdhValue)] -> STM a
throwEdh' !ets !tag !msg !details = do
  let !edhErr = EdhError tag msg errDetails $ getEdhErrCtx 0 ets
  edhWrapException (Just ets) (toException edhErr)
    >>= \ !exo -> edhThrow ets $ EdhObject exo
  where
    !edhWrapException =
      edh'exception'wrapper (edh'prog'world $ edh'thread'prog ets)
    !errDetails = case details of
      [] -> toDyn nil
      _ -> toDyn $ EdhArgsPack $ ArgsPack [] $ odFromList details
{-# INLINE throwEdh' #-}

-- | Throw a tagged error from STM monad, while Edh thread context not available
throwHostSTM :: EdhErrorTag -> Text -> STM a
throwHostSTM !tag !msg = throwHostSTM' tag msg []
{-# INLINE throwHostSTM #-}

-- | Throw a tagged error with some detailed data, from STM monad, while Edh
-- thread context not available
throwHostSTM' ::
  EdhErrorTag -> Text -> [(AttrKey, EdhValue)] -> STM a
throwHostSTM' !tag !msg !details = throwSTM $ EdhHostError tag msg errDetails
  where
    !errDetails = case details of
      [] -> toDyn nil
      _ -> toDyn $ EdhArgsPack $ ArgsPack [] $ odFromList details
{-# INLINE throwHostSTM' #-}

-- | Throw a tagged error from IO monad, while Edh thread context not available
throwHostIO :: EdhErrorTag -> Text -> IO a
throwHostIO !tag !msg = throwHostIO' tag msg []
{-# INLINE throwHostIO #-}

-- | Throw a tagged error with some detailed data, from IO monad, while Edh
-- thread context not available
throwHostIO' ::
  EdhErrorTag -> Text -> [(AttrKey, EdhValue)] -> IO a
throwHostIO' !tag !msg !details = throwIO $ EdhHostError tag msg errDetails
  where
    !errDetails = case details of
      [] -> toDyn nil
      _ -> toDyn $ EdhArgsPack $ ArgsPack [] $ odFromList details
{-# INLINE throwHostIO' #-}

edhThrowTx :: EdhValue -> EdhTx
edhThrowTx = flip edhThrow
{-# INLINE edhThrowTx #-}

-- | Throw arbitrary value from Edh
--
-- a bit similar to `return` in Haskell, this doesn't cease the execution
-- of subsequent actions following it, be cautious.
edhThrow :: EdhThreadState -> EdhValue -> STM a
edhThrow !ets !exv = do
  propagateExc exv $ edh'ctx'tip ctx : edh'ctx'stack ctx
  return undefined
  where
    !ctx = edh'context ets
    propagateExc :: EdhValue -> [EdhCallFrame] -> STM ()
    propagateExc !exv' [] = edhErrorUncaught ets exv'
    propagateExc !exv' (frame : stack) =
      edh'exc'handler frame ets exv' $ \ !exv'' -> propagateExc exv'' stack
{-# INLINE edhThrow #-}

edhErrorUncaught :: EdhThreadState -> EdhValue -> STM a
edhErrorUncaught !ets !exv = case exv of
  EdhObject !exo -> case edh'obj'store exo of
    HostStore !hsd -> case unwrapHostValue hsd of
      Just (exc :: SomeException) -> case edhKnownError exc of
        Just !err -> throwSTM err
        Nothing -> throwSTM $ EdhIOError exc
      _ -> throwDetails
    _ -> throwDetails
  EdhString !msg ->
    throwSTM $ EdhError EvalError msg (toDyn nil) $ getEdhErrCtx 0 ets
  EdhArgsPack (ArgsPack (EdhString !msg : args') !kwargs) ->
    throwSTM $
      EdhError
        EvalError
        msg
        ( toDyn $
            if null args' && odNull kwargs
              then nil
              else EdhArgsPack $ ArgsPack args' kwargs
        )
        $ getEdhErrCtx 0 ets
  _ -> throwDetails
  where
    throwDetails =
      throwSTM $ EdhError EvalError "❌" (toDyn exv) $ getEdhErrCtx 0 ets

-- | Try an Edh action, pass its result to the @passOn@ via `edh'ctx'match`
edhCatchTx ::
  (EdhTxExit EdhValue -> EdhTx) -> -- tryAct
  EdhTxExit EdhValue -> -- normal/recovered exit
  ( EdhTxExit EdhValue -> -- recover exit
    EdhTxExit EdhValue -> -- rethrow exit
    EdhTx
  ) -> -- edh'ctx'match of this Edh tx being the thrown value or nil
  EdhTx
edhCatchTx !tryAct !exit !passOn !etsOuter =
  edhCatch etsOuter tryAct (runEdhTx etsOuter . exit) $
    \ !etsThrower !exv recover rethrow ->
      let !ctxOuter = edh'context etsOuter
          !ctxHndl = ctxOuter {edh'ctx'match = exv}
          !etsHndl = etsThrower {edh'context = ctxHndl}
       in runEdhTx etsHndl $ passOn (const . recover) (const . rethrow)
{-# INLINE edhCatchTx #-}

-- | Try an Edh action, pass its result to the @passOn@
edhCatch ::
  forall a.
  EdhThreadState ->
  (EdhTxExit a -> EdhTx) -> -- tryAct
  (a -> STM ()) -> -- normal/recovered exit
  ( EdhThreadState -> -- thread state of the thrower
    EdhValue -> -- thrown value or nil
    (a -> STM ()) -> -- recover exit
    (EdhValue -> STM ()) -> -- rethrow exit
    STM ()
  ) ->
  STM ()
edhCatch !etsOuter !tryAct !exit !passOn = do
  !handlerThId <- unsafeIOToSTM myThreadId
  let !ctxOuter = edh'context etsOuter
      !frameOuter = edh'ctx'tip ctxOuter
      !tryCtx = ctxOuter {edh'ctx'tip = frameOuter {edh'exc'handler = hndlr}}
      !etsTry = etsOuter {edh'context = tryCtx}

      hndlr :: EdhExcptHndlr
      hndlr !etsThrower !exv !rethrow = do
        !throwerThId <- unsafeIOToSTM myThreadId
        let -- the catch block is providing a result value to recover
            goRecover :: a -> STM ()
            goRecover !result =
              isRecoverable exv >>= \case
                False -> void $ goRethrow exv
                True ->
                  if throwerThId /= handlerThId
                    then -- not on same thread, cease the recovery continuation
                      return ()
                    else -- on the same thread, continue the recovery
                      exit result

            -- the catch block doesn't want to catch this exception, propagate
            -- it outward
            goRethrow :: EdhValue -> STM ()
            goRethrow !exv' =
              edh'exc'handler frameOuter etsThrower exv' rethrow

        passOn etsThrower exv goRecover goRethrow

  runEdhTx etsTry $
    tryAct $ \ !tryResult _ets ->
      -- no exception has occurred, the @passOn@ may be a finally block and we
      -- trigger it here, but expect it to rethow (not to recover)
      passOn
        etsOuter
        EdhNil -- exv
        (const $ error "bug: a finally block trying recovery") -- recover
        (const $ exit tryResult) -- rethrow
  where
    isRecoverable !exv = case exv of
      EdhObject !exo -> case edh'obj'store exo of
        HostStore !hsd -> case unwrapHostValue hsd of
          Just (exc :: SomeException) -> case fromException exc of
            Just ProgramHalt {} -> return False
            _ -> case fromException exc of
              Just ThreadTerminate -> return False
              _ -> return True
          _ -> return True
        _ -> return True
      _ -> return True
{-# INLINE edhCatch #-}

moduleContext :: EdhWorld -> Object -> STM Context
moduleContext !world !modu =
  objectScope modu >>= \ !moduScope -> do
    !moduFile <-
      iopdLookupDefault
        (EdhString "<on-the-fly>")
        (AttrByName "__file__")
        (edh'scope'entity moduScope)
        >>= \case
          EdhString !file -> return file
          _ -> return "<bogus __file__>"
    !tipFrame <- newCallFrame moduScope (SrcLoc (SrcDoc moduFile) zeroSrcRange)
    return $ (worldContext world) {edh'ctx'tip = tipFrame}
{-# INLINE moduleContext #-}

parseEdh ::
  EdhWorld ->
  Text ->
  Text ->
  IO (Either ParserError ([StmtSrc], OptDocCmt))
parseEdh !world !srcName !srcCode = parseEdh' world srcName 1 srcCode

parseEdh' ::
  EdhWorld ->
  Text ->
  Int ->
  Text ->
  IO (Either ParserError ([StmtSrc], OptDocCmt))
parseEdh' !world !srcName !lineNo !srcCode = do
  !pd <- readTVarIO wops
  let ((_, !pr), EdhParserState !pd' _ _) =
        runState
          ( runParserT'
              parseProgram
              State
                { stateInput = srcCode,
                  stateOffset = 0,
                  statePosState =
                    PosState
                      { pstateInput = srcCode,
                        pstateOffset = 0,
                        pstateSourcePos =
                          SourcePos
                            { sourceName = T.unpack srcName,
                              sourceLine = mkPos lineNo,
                              sourceColumn = mkPos 1
                            },
                        pstateTabWidth = mkPos 2,
                        pstateLinePrefix = ""
                      },
                  stateParseErrors = []
                }
          )
          (EdhParserState pd (SrcPos 0 0) 0)
  case pr of
    Right _ -> mergeOpDict wops pd pd'
    -- keep original precedence dict on failure of parsing
    _ -> pure ()
  return pr
  where
    !wops = edh'world'operators world

evalEdh :: Text -> Text -> EdhTxExit EdhValue -> EdhTx
evalEdh !srcName = evalEdh' srcName 1

evalEdh' :: Text -> Int -> Text -> EdhTxExit EdhValue -> EdhTx
evalEdh' !srcName !lineNo !srcCode !exit !ets =
  runEdhTx ets $
    edhContIO $
      parseEdh' world srcName lineNo srcCode >>= \case
        Left !err -> do
          let !msg = T.pack $ errorBundlePretty err
              !edhWrapException = edh'exception'wrapper world
              !edhErr = EdhError ParseError msg (toDyn nil) $ getEdhErrCtx 0 ets
          atomically $
            edhWrapException (Just ets) (toException edhErr)
              >>= \ !exo -> edhThrow ets (EdhObject exo)
        Right (!stmts, _docCmt) ->
          atomically $ runEdhTx etsEval $ evalBlock stmts exit
  where
    !world = edh'prog'world $ edh'thread'prog ets
    !ctx = edh'context ets
    !etsEval =
      ets
        { edh'context =
            ctx
              { edh'ctx'tip =
                  (edh'ctx'tip ctx)
                    { edh'exe'src'loc = SrcLoc (SrcDoc srcName) zeroSrcRange
                    }
              }
        }

withThisHostObj ::
  forall v.
  (Eq v, Hashable v, Typeable v) =>
  EdhThreadState ->
  (v -> STM ()) ->
  STM ()
withThisHostObj !ets =
  withHostInstance ets (edh'scope'this $ contextScope $ edh'context ets)

withThisHostObj' ::
  forall v.
  (Eq v, Hashable v, Typeable v) =>
  EdhThreadState ->
  STM () ->
  (v -> STM ()) ->
  STM ()
withThisHostObj' !ets =
  withHostInstance' (edh'scope'this $ contextScope $ edh'context ets)

withHostInstance ::
  forall v.
  (Eq v, Hashable v, Typeable v) =>
  EdhThreadState ->
  Object ->
  (v -> STM ()) ->
  STM ()
withHostInstance !ets !obj !exit = withHostInstance' obj naExit exit
  where
    naExit =
      throwEdh ets UsageError $
        "not a host object of expected storage type <<"
          <> T.pack (show $ typeRep @v)
          <> ">> but bearing a: "
          <> T.pack (show $ edh'obj'store obj)

withHostInstance' ::
  forall v.
  (Eq v, Hashable v, Typeable v) =>
  Object ->
  STM () ->
  (v -> STM ()) ->
  STM ()
withHostInstance' !obj !naExit !exit = case edh'obj'store obj of
  HostStore !hsd -> case unwrapHostValue hsd of
    Just (hsv :: v) -> exit hsv
    _ -> naExit
  _ -> naExit

withHostObject ::
  forall v.
  (Eq v, Hashable v, Typeable v) =>
  EdhThreadState ->
  Object ->
  (Object -> v -> STM ()) ->
  STM ()
withHostObject !ets !endObj !exit =
  withHostObject'
    endObj
    naExit
    exit
  where
    naExit =
      throwEdh ets UsageError $
        "not derived from a host object of expected storage type: "
          <> T.pack (show $ typeRep @v)

withHostObject' ::
  forall v.
  (Eq v, Hashable v, Typeable v) =>
  Object ->
  STM () ->
  (Object -> v -> STM ()) ->
  STM ()
withHostObject' !endObj !naExit !exit = case edh'obj'store endObj of
  HostStore !hsd -> case unwrapHostValue hsd of
    Just (hsv :: v) -> exit endObj hsv
    _ -> readTVar (edh'obj'supers endObj) >>= checkSupers
  _ -> readTVar (edh'obj'supers endObj) >>= checkSupers
  where
    checkSupers :: [Object] -> STM ()
    checkSupers [] = naExit
    checkSupers (superObj : rest) = case edh'obj'store superObj of
      HostStore !hsd -> case unwrapHostValue hsd of
        Just (hsv :: v) -> exit superObj hsv
        _ -> checkSupers rest
      _ -> checkSupers rest

deExpr' :: Expr -> Expr
deExpr' (ExprWithSrc (ExprSrc !x _) _) = deExpr' x
deExpr' !x = x

deExpr'1 :: Expr -> Expr
deExpr'1 (ExprWithSrc (ExprSrc !x _) _) = x
deExpr'1 !x = x

deExpr :: ExprSrc -> ExprSrc
deExpr (ExprSrc (ExprWithSrc !x _) _) = deExpr x
deExpr !x = x

deExpr1 :: ExprSrc -> ExprSrc
deExpr1 (ExprSrc (ExprWithSrc !x _) _) = x
deExpr1 !x = x

deParen' :: Expr -> Expr
deParen' !x = case x of
  ParenExpr (ExprSrc !x' _) -> deParen' x'
  _ -> x

deParen'1 :: Expr -> Expr
deParen'1 !x = case x of
  ParenExpr (ExprSrc !x' _) -> x'
  _ -> x

deParen :: ExprSrc -> ExprSrc
deParen expr@(ExprSrc !x _) = case x of
  ParenExpr !x' -> deParen x'
  _ -> expr

deParen1 :: ExprSrc -> ExprSrc
deParen1 expr@(ExprSrc !x _) = case x of
  ParenExpr !x' -> x'
  _ -> expr

deApk :: ArgsPack -> ArgsPack
deApk (ArgsPack [EdhArgsPack !apk] !kwargs) | odNull kwargs = deApk apk
deApk x = x

deApk1 :: ArgsPack -> ArgsPack
deApk1 (ArgsPack [EdhArgsPack !apk] !kwargs) | odNull kwargs = apk
deApk1 x = x

evalStmtSrc :: StmtSrc -> EdhTxExit EdhValue -> EdhTx
evalStmtSrc (StmtSrc !stmt !ss) !exit !ets =
  runEdhTx ets {edh'context = ctx {edh'ctx'tip = frameMovePC tip ss}} $
    evalStmt stmt $
      \ !rtn -> edhSwitchState ets $ exit rtn
  where
    !ctx = edh'context ets
    !tip = edh'ctx'tip ctx

edhCaseValueOf :: EdhValue -> ExprDefi -> EdhTxExit EdhValue -> EdhTx
edhCaseValueOf !matchTgtVal (ExprDefi _ !x !src'loc) !exit !ets =
  runEdhTx etsCase $ _evalCaseBranches x $ edhSwitchState ets . exit
  where
    !ctx = edh'context ets
    !tip = edh'ctx'tip ctx
    !etsCase =
      ets
        { edh'context =
            ctx
              { edh'ctx'tip = tip {edh'exe'src'loc = src'loc},
                edh'ctx'match = tv
              }
        }
    !tv = case edhDeCaseClose matchTgtVal of
      EdhCaseOther -> nil
      !v -> v

_evalCaseBranches :: Expr -> EdhTxExit EdhValue -> EdhTx
_evalCaseBranches !x !exit = case x of
  -- case-of with a block is normal
  BlockExpr !stmts -> evalBlock stmts exit
  ScopedBlockExpr !stmts -> evalScopedBlock stmts exit
  -- single branch case is some special
  _ -> evalExpr x $ \ !val -> case val of
    -- the only branch did match, let not the branch match escape
    (EdhCaseClose !v) -> exitEdhTx exit $ edhDeCaseClose v
    -- the only branch didn't match. non-exhaustive case is bad smell in FP,
    -- but kinda norm in imperative style, some equvilant to if-then without an
    -- else clause. anyway the nonmatch should not escape here
    EdhCaseOther -> exitEdhTx exit nil
    -- yield should have been handled by 'evalExpr''
    (EdhYield _) -> throwEdhTx EvalError "bug yield reached block"
    -- ctrl to be propagated outwards, as this is the only stmt, no need to
    -- be specifically written out
    -- EdhFallthrough    -> exitEdhTx exit EdhFallthrough
    -- EdhBreak          -> exitEdhTx exit EdhBreak
    -- EdhContinue       -> exitEdhTx exit EdhContinue
    -- (EdhReturn !v)    -> exitEdhTx exit (EdhReturn v)
    -- other vanilla result, propagate as is
    _ -> exitEdhTx exit val

evalCaseBranches :: EdhValue -> ExprSrc -> EdhTxExit EdhValue -> EdhTx
evalCaseBranches !tgtVal (ExprSrc !x !src'span) !exit !ets =
  runEdhTx (etsMovePC etsCase src'span) $
    _evalCaseBranches x $ edhSwitchState ets . exit
  where
    !etsCase =
      ets
        { edh'context = (edh'context ets) {edh'ctx'match = tv}
        }
    !tv = case edhDeCaseClose tgtVal of
      EdhCaseOther -> nil
      !v -> v

newNestedFrame :: EdhCallFrame -> STM EdhCallFrame
newNestedFrame !baseOnFrame = do
  !s <- newNestedScope $ edh'frame'scope baseOnFrame
  newCallFrame s $ edh'exe'src'loc baseOnFrame

newNestedScope :: Scope -> STM Scope
newNestedScope !baseOnScope = do
  !esAdhoc <- iopdEmpty
  !spid <- newRUID'STM
  return $
    baseOnScope
      { edh'scope'entity = esAdhoc,
        -- the base scope should be the lexical *outer* of the new nested
        -- adhoc scope, required for correct contextual attribute
        -- resolution, and specifically, a `scope()` obtained from within
        -- the nested adhoc scope should have its @.outer@ point to the
        -- base scope
        edh'scope'proc =
          (edh'scope'proc baseOnScope)
            { edh'procedure'ident = spid,
              edh'procedure'lexi = baseOnScope
            }
      }

pushEdhStack' :: Scope -> EdhTx -> EdhTx
pushEdhStack' !scope !act !ets = do
  !tipNew <- newCallFrame scope $ edh'exe'src'loc tip
  let !etsNew = ets {edh'context = ctxNew}
      !ctxNew =
        ctx
          { edh'ctx'tip = tipNew,
            edh'ctx'stack = tip : edh'ctx'stack ctx
          }
  runEdhTx etsNew act
  where
    !ctx = edh'context ets
    !tip = edh'ctx'tip ctx

pushEdhStack :: EdhTx -> EdhTx
pushEdhStack !act !ets = do
  !s <- newNestedScope $ edh'frame'scope $ edh'ctx'tip $ edh'context ets
  pushEdhStack' s act ets

evalScopedBlock :: [StmtSrc] -> EdhTxExit EdhValue -> EdhTx
evalScopedBlock !stmts !exit !ets =
  runEdhTx ets $
    pushEdhStack $
      evalBlock stmts $ edhSwitchState ets . exitEdhTx exit

-- note a branch match should not escape out of a block, so adjacent blocks
-- always execute sequentially
evalBlock :: [StmtSrc] -> EdhTxExit EdhValue -> EdhTx
evalBlock [] !exit = exitEdhTx exit nil
evalBlock [!ss] !exit = evalStmtSrc ss $ \ !val -> case val of
  -- last branch did match
  (EdhCaseClose !v) -> exitEdhTx exit $ edhDeCaseClose v
  -- yield should have been handled by 'evalExpr''
  (EdhYield _) -> throwEdhTx EvalError "bug: yield reached block"
  -- ctrl to be propagated outwards, as this is the last stmt, no need to
  -- be specifically written out
  -- EdhCaseOther      -> exitEdhTx exit EdhCaseOther
  -- EdhFallthrough    -> exitEdhTx exit EdhFallthrough
  -- EdhRethrow        -> exitEdhTx exit EdhRethrow
  -- EdhBreak          -> exitEdhTx exit EdhBreak
  -- EdhContinue       -> exitEdhTx exit EdhContinue
  -- (EdhReturn !v)    -> exitEdhTx exit (EdhReturn v)
  -- other vanilla result, propagate as is
  _ -> exitEdhTx exit val
evalBlock (ss : rest) !exit = evalStmtSrc ss $ \ !val -> case val of
  -- a branch matched, finish this block
  (EdhCaseClose !v) -> exitEdhTx exit $ edhDeCaseClose v
  -- should continue to next branch (or stmt)
  EdhCaseOther -> evalBlock rest exit
  -- should fallthrough to next branch (or stmt)
  EdhFallthrough -> evalBlock rest exit
  -- yield should have been handled by 'evalExpr''
  (EdhYield _) -> throwEdhTx EvalError "bug: yield reached block"
  -- ctrl to interrupt this block, and to be propagated outwards
  EdhRethrow -> exitEdhTx exit EdhRethrow
  EdhBreak -> exitEdhTx exit EdhBreak
  EdhContinue -> exitEdhTx exit EdhContinue
  (EdhReturn !v) -> exitEdhTx exit (EdhReturn v)
  -- other vanilla result, continue this block
  _ -> evalBlock rest exit

-- | a left-to-right expr list eval'er
evalExprs :: [ExprSrc] -> EdhTxExit [EdhValue] -> EdhTx
evalExprs [] !exit = exitEdhTx exit []
evalExprs (x : xs) !exit = evalExprSrc x $ \ !val ->
  evalExprs xs $ exitEdhTx exit . (edhDeFlowCtrl val :)

-- | Evaluate all of its kwargs in case needed
--
-- This is usually useful to host interpreter procedures
evalKwExprs :: KwArgs -> EdhTxExit KwArgs -> EdhTx
evalKwExprs !kwExprs !exit !ets = go [] $ odToList kwExprs
  where
    go :: [(AttrKey, EdhValue)] -> [(AttrKey, EdhValue)] -> STM ()
    go res [] = exitEdh ets exit $ odFromList $ reverse res
    go res ((k, EdhExpr (ExprDefi _ x _) _) : rest) = runEdhTx ets $
      evalExpr x $
        \ !v _ets -> go ((k, v) : res) rest
    go _res ((k, v) : _) =
      throwEdh ets UsageError $
        "non-expr into evalKwExprs: " <> T.pack (show k) <> "= "
          <> T.pack (show v)

evalStmt :: Stmt -> EdhTxExit EdhValue -> EdhTx
evalStmt !stmt !exit = case stmt of
  ExprStmt !expr !docCmt ->
    evalExpr' expr docCmt $ \ !result -> exitEdhTx exit result
  LetStmt !argsRcvr (ArgsPacker !argsSndr _) -> \ !ets -> do
    let !ctx = edh'context ets
        !scope = contextScope ctx
    packEdhArgs ets argsSndr $ \ !apk ->
      recvEdhArgs ets ctx argsRcvr (deApk apk) $ \ !um -> do
        case edh'ctx'eff'target ctx of
          Nothing ->
            -- normal multi-assignment
            iopdUpdate (odToList um) (edh'scope'entity scope)
          Just !esEffs ->
            -- define effectful artifacts by multi-assignment
            -- note that nil can not appear as for arg receiving,
            -- so no processing of delete semantics
            iopdUpdate (odToList um) esEffs
        case edh'ctx'exp'target ctx of
          Nothing -> pure ()
          Just !esExps ->
            -- note that nil can not appear as for arg receiving,
            -- so no processing of delete semantics
            iopdUpdate (odToList um) esExps
        exitEdh ets exit nil -- let statement evaluates to nil always
  BreakStmt -> exitEdhTx exit EdhBreak
  ContinueStmt -> exitEdhTx exit EdhContinue
  FallthroughStmt -> exitEdhTx exit EdhFallthrough
  RethrowStmt -> exitEdhTx exit EdhRethrow
  ReturnStmt !expr !docCmt -> \ !ets ->
    -- use a pure ctx to eval the return expr
    runEdhTx ets {edh'context = (edh'context ets) {edh'ctx'pure = True}} $
      evalExprSrc' expr docCmt $
        -- we are making `return` a sacred ceremony, practical needs include:
        -- that for a generator procedure to "double return" in cooperating
        -- with `yield` from loop body's early return; that for a "decorator"
        -- interpreter procedure to return `break` `continue` etc. for flow
        -- control prupose.
        edhSwitchState ets . exitEdhTx exit . EdhReturn . edhDeCaseClose
  GoStmt expr@(ExprSrc !x !src'span) -> case x of
    CaseExpr !tgtExpr !branchesExpr ->
      evalExprSrc tgtExpr $ \ !val !etsForker ->
        runEdhTx (etsMovePC etsForker src'span) $
          forkEdh
            id
            (evalCaseBranches val branchesExpr endOfEdh)
            $ \() -> exitEdhTx exit nil
    (CallExpr !calleeExpr (ArgsPacker !argsSndr _)) ->
      evalExprSrc calleeExpr $ \ !calleeVal !etsForker -> do
        let !etsForking = etsMovePC etsForker src'span
        edhPrepareCall etsForking calleeVal argsSndr $ \ !mkCall ->
          runEdhTx etsForking $
            forkEdh id (mkCall endOfEdh) $ \() -> exitEdhTx exit nil
    (ForExpr !scoped !argsRcvr !iterExpr !bodyStmt) -> \ !etsForker -> do
      let !etsForking = etsMovePC etsForker src'span
      edhPrepareForLoop
        etsForking
        scoped
        argsRcvr
        iterExpr
        bodyStmt
        (const $ return ())
        $ \ !iterVal !runLoop -> case iterVal of
          EdhSink !sink -> do
            -- @remind assuming sync-producing semantics, the for-loop to
            -- be forked is assumed the consumer, here we wait the sink
            -- get subscribed by it, before continuing current thread
            let !subc = sink'subc sink
            !subcBefore <- readTVar subc
            if subcBefore < 0
              then exitEdh etsForking exit nil -- the sink alread at eos
              else runEdhTx etsForking $
                forkEdh id (runLoop endOfEdh) $ \() -> edhContSTM $ do
                  !subcNow <- readTVar subc
                  when (subcNow == subcBefore) retry
                  exitEdh etsForking exit nil
          _ -> runEdhTx etsForking $
            forkEdh id (runLoop endOfEdh) $ \() -> exitEdhTx exit nil
    _ -> forkEdh id (evalExprSrc expr endOfEdh) $ \() -> exitEdhTx exit nil
  DeferStmt (ExprSrc !expr !src'span) -> do
    let schedDefered ::
          EdhThreadState ->
          (EdhThreadState -> EdhThreadState) ->
          EdhTx ->
          STM ()
        schedDefered !etsSched !bootMod !etx = do
          modifyTVar'
            (edh'defers etsSched)
            ((DeferRecord (etsMovePC etsSched src'span) $ etx . bootMod) :)
          runEdhTx etsSched $ exit nil

    case expr of
      CaseExpr !tgtExpr !branchesExpr ->
        evalExprSrc tgtExpr $ \ !val !etsSched ->
          schedDefered
            etsSched
            id
            $ evalCaseBranches val branchesExpr endOfEdh
      (CallExpr !calleeExpr (ArgsPacker !argsSndr _)) ->
        evalExprSrc calleeExpr $ \ !calleeVal !etsSched ->
          edhPrepareCall etsSched calleeVal argsSndr $
            \ !mkCall -> schedDefered etsSched id (mkCall endOfEdh)
      (ForExpr !scoped !argsRcvr !iterExpr !bodyStmt) -> \ !etsSched ->
        edhPrepareForLoop
          etsSched
          scoped
          argsRcvr
          iterExpr
          bodyStmt
          (const $ return ())
          $ \_iterVal !runLoop ->
            schedDefered etsSched id (runLoop endOfEdh)
      _ -> \ !etsSched ->
        schedDefered etsSched id $ evalExpr' expr NoDocCmt endOfEdh
  PerceiveStmt !sinkExpr bodyExpr@(ExprSrc body'x body'rng) ->
    evalExprSrc sinkExpr $ \ !sinkVal !ets -> case edhUltimate sinkVal of
      EdhSink !sink ->
        if edh'in'tx ets
          then do
            modifyTVar' (sink'atoms sink) $ \ !prev'atoms !ev ->
              runEdhTx
                ets {edh'context = (edh'context ets) {edh'ctx'match = ev}}
                $ evalExprSrc bodyExpr $ \_ _ets -> prev'atoms ev
            exitEdh ets exit nil
          else do
            let reactor !breakThread =
                  evalExprSrc bodyExpr $ \ !reactResult _etsReactor ->
                    case edhDeCaseClose reactResult of
                      EdhBreak -> writeTVar breakThread True
                      -- todo warn or even err out in case
                      -- return/continue/default etc. are returned to here?
                      _ -> return ()
            subscribeEvents sink >>= \case
              Nothing -> case sink'mrv sink of -- already at eos
                Nothing -> pure () -- non-lingering, nothing to do
                Just {} ->
                  -- a lingering sink, trigger an immediate nil perceiving
                  runEdhTx ets $
                    edhContIO' $
                      drivePerceiver nil ets reactor id
              Just (!perceiverChan, !lingerVal) -> do
                modifyTVar'
                  (edh'perceivers ets)
                  (PerceiveRecord perceiverChan ets reactor :)
                case lingerVal of
                  Nothing -> pure ()
                  Just !mrv ->
                    -- mrv lingering, trigger an immediate perceiving
                    runEdhTx ets $
                      edhContIO' $
                        drivePerceiver mrv ets reactor id
            exitEdh ets exit nil
      EdhObject !sinkLikeObj -> do
        let SrcLoc !doc _pos = edh'exe'src'loc $ edh'ctx'tip $ edh'context ets
        !u <- newRUID'STM
        runEdhTx ets $
          invokeMagic
            sinkLikeObj
            (AttrByName "__perceive__")
            ( ArgsPack
                [EdhExpr (ExprDefi u body'x (SrcLoc doc body'rng)) ""]
                odEmpty
            )
            (exitEdhTx exit)
            ($)
      _ -> edhSimpleDesc ets sinkVal $ \ !badDesc ->
        throwEdh ets EvalError $ "not perceivable: " <> badDesc
  ThrowStmt !excExpr ->
    evalExprSrc excExpr $ \ !exv -> edhThrowTx $ edhDeCaseClose exv
  ExtendsStmt !superExpr -> evalExprSrc superExpr $ \ !superVal !ets ->
    let !this = edh'scope'this $ contextScope $ edh'context ets
     in case edhDeCaseClose superVal of
          EdhObject !superObj ->
            edhObjExtends ets this superObj $ exitEdh ets exit nil
          EdhArgsPack (ArgsPack !supers !kwargs)
            | odNull kwargs ->
              let extendSupers :: [EdhValue] -> STM ()
                  extendSupers [] = exitEdh ets exit nil
                  extendSupers (val : rest) = case val of
                    EdhObject !superObj ->
                      edhObjExtends ets this superObj $ extendSupers rest
                    _ -> edhValueStr ets val $ \ !superStr ->
                      throwEdh ets UsageError $
                        "can not extends a "
                          <> edhTypeNameOf val
                          <> ": "
                          <> superStr
               in extendSupers supers
          _ -> edhSimpleDesc ets superVal $ \ !badDesc ->
            throwEdh ets UsageError $
              "can not extend a " <> badDesc
  EffectStmt !effs !docCmt -> \ !ets -> do
    !esEffs <-
      prepareEffStore ets $ edh'scope'entity $ contextScope $ edh'context ets
    runEdhTx
      ets
        { edh'context = (edh'context ets) {edh'ctx'eff'target = Just esEffs}
        }
      $ evalExprSrc' effs docCmt $
        \ !rtn -> edhSwitchState ets $ exit rtn
  VoidStmt -> exitEdhTx exit nil
  UnitStmt !decls !docCmt -> \ !ets ->
    case edh'ctx'eff'target $ edh'context ets of
      Just {} -> throwEdh ets UsageError "uom is always lexical, not effectful"
      Nothing -> do
        let defineUnits :: [UnitDecl] -> STM ()
            defineUnits [] = exitEdh ets exit nil
            defineUnits (ud : rest) = runEdhTx ets $
              defineUnit docCmt ud $ \_ _ets -> defineUnits rest
        defineUnits decls
  IllegalSegment !err'msg !err'pos -> \ !ets -> do
    let SrcLoc !doc _pos = edh'exe'src'loc $ edh'ctx'tip $ edh'context ets
    -- todo add tolerating mode?
    throwEdh ets EvalError $
      "illegal code at: " <> prettySrcPos doc err'pos <> "\n" <> err'msg

defineUnit :: OptDocCmt -> UnitDecl -> EdhTxExit NamedUnitDefi -> EdhTx
defineUnit !docCmt !decl !exit !ets = case decl of
  PrimUnitDecl sym _ ->
    defineFormula True sym Nothing $ exitEdh ets exit
  ConversionFactor nQty nSym _nSpan dQty dUnit ->
    defineFormula
      False
      nSym
      (Just (unitSpecWithoutSrc dUnit, RatioFormula $ nQty / dQty))
      $ \ !defi -> case dUnit of
        NamedUnitSrc dSym _ | not (T.null dSym) ->
          defineFormula
            False
            dSym
            (Just (NamedUnit nSym, RatioFormula $ dQty / nQty))
            $ \_ -> exitEdh ets exit defi
        _ -> exitEdh ets exit defi
  ConversionFormula outSym _ (ExprSrc !x !x'span) fSrc inSym -> do
    !u <- newRUID'STM
    let curSrcLoc = edh'exe'src'loc $ edh'ctx'tip $ edh'context ets
        formulaDefi = ExprDefi u x curSrcLoc {src'range = x'span}
    defineFormula
      False
      outSym
      (Just (NamedUnit inSym, ExprFormula formulaDefi fSrc))
      $ exitEdh ets exit
  where
    !ctx = edh'context ets
    !scope = contextScope ctx

    -- Note we intentionally do not update the UoM definition in outer scopes,
    --      if already defined there, a new definition incorporating existing
    --      formulae is always inserted into current scope.
    defineFormula ::
      Bool ->
      AttrName ->
      Maybe (UnitSpec, UnitFormula) ->
      (NamedUnitDefi -> STM ()) ->
      STM ()
    defineFormula prim sym Nothing !exit' =
      resolveEdhCtxAttr scope (AttrByName sym) >>= \case
        Nothing -> do
          let defi = NamedUnitDefi docCmt prim sym []
          iopdInsert (AttrByName sym) (EdhUoM $ NamedUnitDefi' defi) $
            edh'scope'entity scope
          case edh'ctx'exp'target ctx of
            Nothing -> pure ()
            Just !esExps ->
              iopdInsert (AttrByName sym) (EdhUoM $ NamedUnitDefi' defi) esExps
          exit' defi
        Just
          ( EdhUoM
              ( NamedUnitDefi'
                  (NamedUnitDefi prevCmt prevPrim defiSym prevFormulae)
                ),
            _prevScope
            )
            | defiSym == sym -> do
              let defi =
                    NamedUnitDefi
                      (mergeDocCmts prevCmt docCmt)
                      (prim || prevPrim)
                      sym
                      prevFormulae
              case docCmt of
                NoDocCmt -> pure ()
                _ ->
                  iopdInsert (AttrByName sym) (EdhUoM $ NamedUnitDefi' defi) $
                    edh'scope'entity scope
              case edh'ctx'exp'target ctx of
                Nothing -> pure ()
                Just !esExps ->
                  iopdInsert
                    (AttrByName sym)
                    (EdhUoM $ NamedUnitDefi' defi)
                    esExps
              exit' defi
        Just (badVal, _) -> edhSimpleDesc ets badVal $ \ !badDesc ->
          throwEdh ets UsageError $
            "can not re-define as UoM [" <> sym <> "] from: " <> badDesc
    defineFormula prim sym (Just (srcUoM, uf)) !exit' =
      resolveEdhCtxAttr scope (AttrByName sym) >>= \case
        Nothing -> do
          let defi = NamedUnitDefi docCmt prim sym [(srcUoM, uf)]
          iopdInsert (AttrByName sym) (EdhUoM $ NamedUnitDefi' defi) $
            edh'scope'entity scope
          case edh'ctx'exp'target ctx of
            Nothing -> pure ()
            Just !esExps ->
              iopdInsert (AttrByName sym) (EdhUoM $ NamedUnitDefi' defi) esExps
          exit' defi
        Just
          ( EdhUoM
              ( NamedUnitDefi'
                  (NamedUnitDefi prevCmt prevPrim defiSym prevFormulae)
                ),
            _prevScope
            )
            | defiSym == sym -> do
              let defi =
                    NamedUnitDefi
                      (mergeDocCmts prevCmt docCmt)
                      (prim || prevPrim)
                      sym
                      $ mergeFormulaInto srcUoM uf prevFormulae
              iopdInsert (AttrByName sym) (EdhUoM $ NamedUnitDefi' defi) $
                edh'scope'entity scope
              case edh'ctx'exp'target ctx of
                Nothing -> pure ()
                Just !esExps ->
                  iopdInsert
                    (AttrByName sym)
                    (EdhUoM $ NamedUnitDefi' defi)
                    esExps
              exit' defi
        Just (badVal, _) -> edhSimpleDesc ets badVal $ \ !badDesc ->
          throwEdh ets UsageError $
            "can not define UoM [" <> sym <> "] into: " <> badDesc

    mergeFormulaInto ::
      UnitSpec ->
      UnitFormula ->
      [(UnitSpec, UnitFormula)] ->
      [(UnitSpec, UnitFormula)]
    mergeFormulaInto u f l = nubBy (\(u1, _) (u2, _) -> u1 == u2) $ case f of
      RatioFormula r -> do
        let go rfs [] = reverse $! (u, f) : rfs
            go rfs l'@(e@(_, f') : rest) = case f' of
              RatioFormula r' ->
                if r' < r
                  then go (e : rfs) rest
                  else (reverse $! rfs) ++ (u, f) : l'
              ExprFormula {} -> (reverse $! rfs) ++ (u, f) : l'
        go [] l
      ExprFormula {} -> do
        let go rfs [] = reverse $! (u, f) : rfs
            go rfs l'@(e@(_, f') : rest) = case f' of
              RatioFormula {} -> go (e : rfs) rest
              ExprFormula {} -> (reverse $! rfs) ++ (u, f) : l'
        go [] l

mustUnifyToUnit :: UnitDefi -> EdhValue -> EdhTxExit Decimal -> EdhTx
mustUnifyToUnit !uom !val exit = case edhUltimate val of
  EdhDecimal q ->
    unifyToUnit uom (Left q) exit $
      throwEdhTx UsageError $
        "can not unify a pure number to UoM [" <> uomDefiIdent uom <> "]"
  EdhQty qty -> unifyToUnit uom (Right qty) exit $
    edhSimpleDescTx val $ \ !badDesc ->
      throwEdhTx UsageError $
        "can not unify " <> badDesc <> " to UoM [" <> uomDefiIdent uom <> "]"
  _ -> edhSimpleDescTx val $ \ !badDesc ->
    throwEdhTx UsageError $ "can only unify quantities, not a " <> badDesc

unifyToUnit ::
  UnitDefi -> Either Decimal Quantity -> EdhTxExit Decimal -> EdhTx -> EdhTx
unifyToUnit tgtUoM (Left d) exit naExit =
  if isUnitless tgtUoM
    then exitEdhTx exit d
    else case tgtUoM of
      NamedUnitDefi' ud -> go $ uom'defi'formulae ud
      ArithUnitDefi {} -> naExit
  where
    go [] = naExit
    go ((_, ExprFormula {}) : rest) = go rest
    go ((srcUoM, RatioFormula r) : rest) =
      if isUnitlessSpec srcUoM
        then exitEdhTx exit $ d * r
        else go rest
unifyToUnit (NamedUnitDefi' u) (Right q) exit naExit =
  qtyUnifyToNamed u q exit naExit
unifyToUnit ArithUnitDefi {} Right {} _exit naExit =
  naExit -- TODO implement this case

qtyUnifyToNamed ::
  NamedUnitDefi ->
  Quantity ->
  EdhTxExit Decimal ->
  EdhTx ->
  EdhTx
qtyUnifyToNamed = doUnify Map.empty
  where
    doUnify ::
      Map.HashMap AttrName Bool ->
      NamedUnitDefi ->
      Quantity ->
      EdhTxExit Decimal ->
      EdhTx ->
      EdhTx
    doUnify visited tgtUnit qty@(Quantity q srcUoM) exit naExit =
      if srcUnitIdent == tgtUnitIdent
        then exitEdhTx exit q -- shortcut
        else do
          let fl = uom'defi'formulae tgtUnit

              tryIndirect :: [(UnitSpec, UnitFormula)] -> EdhTx
              tryIndirect [] = naExit
              tryIndirect ((u, formula) : rest) =
                case Map.lookup (uomSpecIdent u) visited of
                  Just {} -> tryIndirect rest
                  Nothing -> resolveUnitSpec u $ \case
                    NamedUnitDefi' bridgeUnit ->
                      doUnify
                        visited'
                        bridgeUnit
                        qty
                        (exitByConverting formula $ uom'defi'sym bridgeUnit)
                        $ tryIndirect rest
                    ArithUnitDefi {} -> tryIndirect rest

              tryDirect :: [(UnitSpec, UnitFormula)] -> EdhTx
              tryDirect [] = tryIndirect fl
              tryDirect ((u, formula) : rest) =
                if uomSpecIdent u == srcUnitIdent
                  then exitByConverting formula srcUnitIdent q
                  else tryDirect rest

          tryDirect fl
      where
        tgtUnitIdent = uom'defi'sym tgtUnit
        visited' = Map.insert tgtUnitIdent True visited
        srcUnitIdent = uomDefiIdent srcUoM

        exitByConverting :: UnitFormula -> AttrName -> Decimal -> EdhTx
        exitByConverting f uomIdent d = case f of
          RatioFormula r -> exit $ d * r
          ExprFormula x _ -> evalUnitFormula d uomIdent x exit

evalUnitFormula :: Decimal -> AttrName -> ExprDefi -> EdhTxExit Decimal -> EdhTx
evalUnitFormula d uomIdent x exit !ets = runEdhTx ets $
  pushEdhStack $ \ !ets' -> do
    iopdInsert (AttrByName $ "[" <> uomIdent <> "]") (EdhDecimal d) $
      edh'scope'entity $ contextScope $ edh'context ets'
    runEdhTx ets' $
      evalExprDefi x $ \case
        EdhDecimal rd -> \_ets -> exitEdh ets exit rd
        badVal -> edhSimpleDescTx badVal $ \badDesc ->
          throwEdhTx EvalError $ "UoM formula gives bad result: " <> badDesc

qtyToPureNumber :: Quantity -> EdhTxExit (Maybe Decimal) -> EdhTx
qtyToPureNumber (Quantity q u) exit =
  if isUnitless u
    then exitEdhTx exit $ Just q
    else case u of
      ArithUnitDefi {} -> exitEdhTx exit Nothing
      NamedUnitDefi' ud -> go $ uom'defi'formulae ud
  where
    go [] = exitEdhTx exit Nothing
    go ((uSpec, formula) : rest) =
      if isUnitlessSpec uSpec
        then case formula of
          RatioFormula r -> exitEdhTx exit $ Just $ q / r
          ExprFormula {} -> go rest
        else go rest

unifyToPrimUnit ::
  Quantity -> EdhTxExit (Either Decimal Quantity) -> EdhTx -> EdhTx
unifyToPrimUnit qty@(Quantity q0 u0) exit naExit
  | isUnitless u0 = exitEdhTx exit $ Left q0
  | isPrimaryUnit u0 = exitEdhTx exit $ Right qty
  | otherwise = tryUnits (Just u0) empty
  where
    -- todo: optimize perf by leveraging conversion paths of ratio formulae
    tryUnits ::
      Maybe UnitDefi -> Deque (UnitDefi, UnitSpec, UnitFormula) -> EdhTx
    tryUnits Nothing backlog = case Deque.uncons backlog of
      Nothing -> naExit
      Just ((uomBridge, uomSpec, formula), backlog') ->
        if isUnitlessSpec uomSpec
          then case formula of
            RatioFormula r ->
              -- convertible to dimensionless via this bridge unit
              unifyToUnit
                uomBridge
                (Right qty)
                (\d -> exitEdhTx exit $ Left $ d / r)
                (tryUnits Nothing backlog')
            ExprFormula {} ->
              -- no way of reverse conversion
              tryUnits Nothing backlog'
          else resolveUnitSpec uomSpec $ \uom ->
            tryUnits (Just uom) backlog'
    tryUnits (Just uom) backlog = case uom of
      NamedUnitDefi' ud ->
        if uom'defi'prim ud
          then
            unifyToUnit
              uom
              (Right qty)
              (exitEdhTx exit . Right . flip Quantity uom)
              tryMore
          else tryMore
      ArithUnitDefi ns ds -> do
        let tryList ::
              [NamedUnitDefi] ->
              [NamedUnitDefi] ->
              Decimal ->
              [NamedUnitDefi] ->
              EdhTxExit (Decimal, [NamedUnitDefi], [NamedUnitDefi]) ->
              EdhTx
            tryList ns' ds' r [] exit' = exit' (r, ns', ds')
            tryList ns' ds' r (ud : rest) exit' =
              unifyToPrimUnit
                (Quantity r $ NamedUnitDefi' ud)
                ( \case
                    Left d -> tryList ns' ds' d rest exit'
                    Right (Quantity q' u') -> case u' of
                      NamedUnitDefi' ud' ->
                        tryList (ns' ++ [ud']) ds' q' rest exit'
                      ArithUnitDefi ns'' ds'' ->
                        tryList (ns' ++ ns'') (ds' ++ ds'') q' rest exit'
                )
                tryMore
        tryList [] [] 1 ns $ \(nr, nns, nds) ->
          tryList [] [] 1 ds $ \(dr, dns, dds) ->
            normalizeArithUnit (nns ++ dds) (nds ++ dns) $ \(normR, normUoM) ->
              exitEdhTx exit $ Right $ Quantity (normR * q0 * nr / dr) normUoM
      where
        tryMore = tryUnits Nothing $ case uom of
          NamedUnitDefi' ud ->
            (backlog <>) $
              fromList $
                (<$> uom'defi'formulae ud) $
                  \(uomSpec, formula) -> (uom, uomSpec, formula)
          ArithUnitDefi {} -> backlog

normalizeUnit :: UnitDefi -> EdhTxExit (Decimal, UnitDefi) -> EdhTx
normalizeUnit (NamedUnitDefi' ud) exit = exit (1, NamedUnitDefi' ud)
normalizeUnit (ArithUnitDefi ns ds) exit = normalizeArithUnit ns ds exit

normalizeArithUnit ::
  [NamedUnitDefi] -> [NamedUnitDefi] -> EdhTxExit (Decimal, UnitDefi) -> EdhTx
normalizeArithUnit [] [] exit0 = exit0 (1, unitlessUnit)
normalizeArithUnit [ud] [] exit0 = exit0 (1, NamedUnitDefi' ud)
normalizeArithUnit ns0 ds0 exit0 =
  unifyNamedUnits ns0 $ \(nr, ns0') ->
    unifyNamedUnits ds0 $ \(dr, ds0') ->
      reduceArithUnits ns0' ds0' $ \(ar, ns0'', ds0'') -> do
        let r = nr / dr * ar
        exit0 $ case dcntUnits [] [] $ mergeUnits [] ns0'' ds0'' of
          ([], []) -> (r, unitlessUnit)
          ([ud], []) -> (r, NamedUnitDefi' ud)
          (ns, ds) -> (r, ArithUnitDefi ns ds)
  where
    mergeUnits ::
      [(NamedUnitDefi, Int)] ->
      [NamedUnitDefi] ->
      [NamedUnitDefi] ->
      [(NamedUnitDefi, Int)]
    mergeUnits cs [] [] = cs
    mergeUnits cs (nu : rest) ds =
      mergeUnits (ecntUnit nu (+ 1) cs) rest ds
    mergeUnits cs [] (du : rest) =
      mergeUnits (ecntUnit du (subtract 1) cs) [] rest

    ecntUnit ::
      NamedUnitDefi ->
      (Int -> Int) ->
      [(NamedUnitDefi, Int)] ->
      [(NamedUnitDefi, Int)]
    ecntUnit u t cs = go [] cs
      where
        go vs [] = reverse $ (u, t 0) : vs
        go vs (e@(u', c) : rest) =
          if u == u'
            then reverse ((u, t c) : vs) ++ rest
            else go (e : vs) rest

    dcntUnits ::
      [NamedUnitDefi] ->
      [NamedUnitDefi] ->
      [(NamedUnitDefi, Int)] ->
      ([NamedUnitDefi], [NamedUnitDefi])
    dcntUnits ns ds [] = (ns, ds)
    dcntUnits ns ds ((u, n) : rest)
      | n > 0 = dcntUnits (ns ++ replicate n u) ds rest
      | n < 0 = dcntUnits ns (ds ++ replicate (- n) u) rest
      | otherwise = dcntUnits ns ds rest -- n == 0

    -- unify units in the list those convertible to eachothers
    --
    -- a ratio formula between 2 named units is bidirectional, so we don't need
    -- to scan the list another (reversed) pass.
    unifyNamedUnits ::
      [NamedUnitDefi] -> EdhTxExit (Decimal, [NamedUnitDefi]) -> EdhTx
    unifyNamedUnits us exit = go1 1 [] us
      where
        go1 r1 rs1 [] = exit (r1, reverse rs1)
        go1 r1 rs1 [u1] = go1 r1 (u1 : rs1) []
        go1 r1 rs1 (u1 : rest1) = go2 [] r1 rest1
          where
            go2 rs2 r2 [] = go1 r2 (u1 : rs1) (reverse rs2)
            go2 rs2 r2 (u2 : rest2) =
              qtyUnifyToNamed
                u1
                (Quantity 1 $ NamedUnitDefi' u2)
                (\r -> go2 (u1 : rs2) (r2 * r) rest2)
                (go2 (u2 : rs2) r2 rest2)

    reduceArithUnits ::
      [NamedUnitDefi] ->
      [NamedUnitDefi] ->
      EdhTxExit (Decimal, [NamedUnitDefi], [NamedUnitDefi]) ->
      EdhTx
    reduceArithUnits ns1 ds1 exit = go1 [] [] 1 ns1 ds1
      where
        go1 rns rds r1 [] ds = exit (r1, reverse rns, reverse rds ++ ds)
        go1 rns rds r1 ns [] = exit (r1, reverse rns ++ ns, reverse rds)
        go1 rns rds r1 (nu : rest1) ds = go2 [] r1 ds
          where
            go2 rs r2 [] = go1 (nu : rns) rds r2 rest1 (reverse rs)
            go2 rs r2 (du : rest2) =
              qtyUnifyToNamed
                nu
                (Quantity 1 $ NamedUnitDefi' du)
                (\r -> go1 rns rds (r2 / r) rest1 (reverse rs ++ rest2))
                (go2 (du : rs) r2 rest2)

-- | Unitless unit, effectively the dimensionless one (1)
unitlessUnit :: UnitDefi
unitlessUnit = NamedUnitDefi' $ NamedUnitDefi NoDocCmt True "" []

qtyMul :: Quantity -> Quantity -> EdhTxExit (Either Decimal Quantity) -> EdhTx
qtyMul qty1@(Quantity q1 u01) qty2@(Quantity q2 u02) exit =
  qtyExpandUnits qty1 $ \case
    Left d1 ->
      exitEdhTx exit $ Right $ Quantity (d1 * q2) u02
    Right (Quantity q1' u01') -> qtyExpandUnits qty2 $ \case
      Left d2 ->
        exitEdhTx exit $ Right $ Quantity (q1 * d2) u01
      Right (Quantity q2' u02') ->
        uncurry normalizeArithUnit (uomMul u01' u02') $ \(normR, normUoM) ->
          if isUnitless normUoM
            then exitEdhTx exit $ Left (normR * q1' * q2')
            else exitEdhTx exit $ Right $ Quantity (normR * q1' * q2') normUoM
  where
    uomMul :: UnitDefi -> UnitDefi -> ([NamedUnitDefi], [NamedUnitDefi])
    uomMul (NamedUnitDefi' u1) (NamedUnitDefi' u2) = ([u1, u2], [])
    uomMul (NamedUnitDefi' u1) (ArithUnitDefi ns ds) = (u1 : ns, ds)
    uomMul (ArithUnitDefi ns ds) (NamedUnitDefi' u2) = (ns ++ [u2], ds)
    uomMul (ArithUnitDefi ns1 ds1) (ArithUnitDefi ns2 ds2) =
      (ns1 ++ ns2, ds1 ++ ds2)

qtyDiv :: Quantity -> Quantity -> EdhTxExit (Either Decimal Quantity) -> EdhTx
qtyDiv qty1@(Quantity q1 u01) qty2@(Quantity q2 u02) exit =
  qtyExpandUnits qty1 $ \r1 -> qtyExpandUnits qty2 $ \r2 ->
    case r1 of
      Left d1 -> case r2 of
        Left d2 ->
          exitEdhTx exit $ Left $ d1 / d2
        Right Quantity {} ->
          normalizeUnit (uomReciprocal u02) $ \(normR, normUoM) ->
            exitEdhTx exit $ Right $ Quantity (normR * d1 / q2) normUoM
      Right (Quantity q1' u01') -> case r2 of
        Left d2 ->
          exitEdhTx exit $ Right $ Quantity (q1 / d2) u01
        Right (Quantity q2' u02') ->
          uncurry normalizeArithUnit (uomDiv u01' u02') $ \(normR, normUoM) ->
            if isUnitless normUoM
              then exitEdhTx exit $ Left (normR * q1' / q2')
              else exitEdhTx exit $ Right $ Quantity (normR * q1' / q2') normUoM
  where
    uomDiv :: UnitDefi -> UnitDefi -> ([NamedUnitDefi], [NamedUnitDefi])
    uomDiv (NamedUnitDefi' u1) (NamedUnitDefi' u2) = ([u1], [u2])
    uomDiv (NamedUnitDefi' u1) (ArithUnitDefi ns ds) = (u1 : ds, ns)
    uomDiv (ArithUnitDefi ns ds) (NamedUnitDefi' u2) = (ns, ds ++ [u2])
    uomDiv (ArithUnitDefi ns1 ds1) (ArithUnitDefi ns2 ds2) =
      (ns1 ++ ds2, ds1 ++ ns2)

qtyExpandUnits :: Quantity -> EdhTxExit (Either Decimal Quantity) -> EdhTx
qtyExpandUnits (Quantity q0 u0) exit0 = doExpand u0 $ \case
  Left r -> exit0 $ Left (q0 / r)
  Right (r, ns, ds) -> normalizeArithUnit ns ds $ \(normR, normUoM) -> do
    let qty = Quantity (normR * q0 / r) normUoM
    unifyToPrimUnit qty exit0 $ exit0 $ Right qty
  where
    doExpand ::
      UnitDefi ->
      EdhTxExit (Either Decimal (Decimal, [NamedUnitDefi], [NamedUnitDefi])) ->
      EdhTx
    doExpand u exit =
      if isUnitless u
        then exit $ Left 1 -- unitless
        else case u of
          NamedUnitDefi' ud -> expandNamed ud exit
          ArithUnitDefi ns ds -> expandArith ns ds $ exit . Right

    expandArith ::
      [NamedUnitDefi] ->
      [NamedUnitDefi] ->
      EdhTxExit (Decimal, [NamedUnitDefi], [NamedUnitDefi]) ->
      EdhTx
    expandArith ns1 ds1 exit1 = go ns1 ds1 exit1
      where
        go [] [] exit = exit (1, [], [])
        go (u : rest) ds exit = expandNamed u $ \case
          Left r -> go rest ds $ \(r', xns, xds) ->
            exit (r' * r, xns, xds)
          Right (r, xns, xds) -> go rest ds $ \(r', xns', xds') ->
            exit (r' * r, xns ++ xns', xds ++ xds')
        go [] (u : rest) exit = expandNamed u $ \case
          Left r -> go [] rest $ \(r', xns, xds) ->
            exit (r' / r, xns, xds)
          Right (r, xns, xds) -> go [] rest $ \(r', xns', xds') ->
            exit (r' / r, xds ++ xns', xns ++ xds')

    expandNamed ::
      NamedUnitDefi ->
      EdhTxExit (Either Decimal (Decimal, [NamedUnitDefi], [NamedUnitDefi])) ->
      EdhTx
    expandNamed ud exit = go $ uom'defi'formulae ud
      where
        go [] = exit $ Right (1, [ud], [])
        go ((uomSpec, formula) : rest) =
          if isUnitlessSpec uomSpec
            then case formula of
              RatioFormula r -> exit $ Left r
              ExprFormula {} -> go rest
            else case formula of
              RatioFormula r -> case uomSpec of
                NamedUnit {} -> go rest
                ArithUnit {} ->
                  resolveUnitSpec uomSpec $
                    flip doExpand $ \case
                      Left r' -> exit $ Left (r * r')
                      Right (r', ns, ds) -> exit $ Right (r * r', ns, ds)
              ExprFormula {} -> go rest

-- | Reduce the absolute scale of the number for a quantity
--
-- Try converting to some larger or smaller unit, with the goal for the number
-- to be within `0.9 ~ 10` scale.
reduceQtyNumber :: Quantity -> EdhTxExit Quantity -> EdhTx -> EdhTx
reduceQtyNumber qty@(Quantity q uom) exit naExit
  | not $ D.decimalIsFinite q = exit qty
  | qv > 0.9 && qv < 10 =
    exitEdhTx exit qty -- already in good scale, return as is
  | otherwise = case uom of
    NamedUnitDefi' ud -> do
      let fl = uom'defi'formulae ud
      if qv <= 0.9
        then upScale fl naExit
        else -- i.e. qv >= 10
          dnScale (reverse fl) naExit
    ArithUnitDefi _nuds _duds ->
      naExit -- TODO impl. this case
  where
    qv = abs q

    upScale :: [(UnitSpec, UnitFormula)] -> EdhTx -> EdhTx
    upScale [] fbExit = fbExit
    upScale ((_, ExprFormula {}) : _) fbExit = fbExit
    upScale ((tgtSpec, RatioFormula r) : rest) fbExit = do
      let q' = q / r
          qv' = abs q'
      if qv' <= qv || (qv' >= 10 && qv' > 10 / qv)
        then fbExit
        else upScale rest $
          resolveUnitSpec tgtSpec $ \ !tgtUoM -> do
            let qty' = Quantity q' tgtUoM
            reduceQtyNumber qty' exit $ exitEdhTx exit qty'

    dnScale :: [(UnitSpec, UnitFormula)] -> EdhTx -> EdhTx
    dnScale [] fbExit = fbExit
    dnScale ((_, ExprFormula {}) : rest) fbExit = dnScale rest fbExit
    dnScale ((tgtSpec, RatioFormula r) : rest) fbExit = do
      let q' = q / r
          qv' = abs q'
      if qv' >= qv || (qv' <= 0.9 && qv' < 10 / qv)
        then fbExit
        else dnScale rest $
          resolveUnitSpec tgtSpec $ \ !tgtUoM -> do
            let qty' = Quantity q' tgtUoM
            reduceQtyNumber qty' exit $ exitEdhTx exit qty'

type CheckImportExternalModule = Text -> EdhTx -> EdhTx

importInto ::
  CheckImportExternalModule ->
  EntityStore ->
  Object ->
  ArgsReceiver ->
  ExprSrc ->
  EdhTxExit EdhValue ->
  EdhTx
importInto !chkExtImp !tgtEnt !reExpObj !argsRcvr srcExpr@(ExprSrc x _) !exit =
  case x of
    LitExpr (StringLiteral !importSpec) ->
      -- import from specified path
      chkExtImp importSpec $
        importEdhModule'
          tgtEnt
          reExpObj
          argsRcvr
          importSpec
          (exit . EdhObject)
    _ -> evalExprSrc srcExpr $ \ !srcVal -> case edhDeCaseClose srcVal of
      EdhString !importSpec ->
        -- import from dynamic path
        chkExtImp importSpec $
          importEdhModule'
            tgtEnt
            reExpObj
            argsRcvr
            importSpec
            (exit . EdhObject)
      EdhObject !fromObj -> \ !ets -> -- import from an object
        runEdhTx ets $
          importFromObject tgtEnt reExpObj argsRcvr fromObj $
            exitEdh ets exit $ EdhObject fromObj
      EdhArgsPack !fromApk -> \ !ets -> -- import from an argument pack
        runEdhTx ets $
          importFromApk tgtEnt reExpObj argsRcvr fromApk $
            exitEdh ets exit $
              EdhArgsPack fromApk
      -- todo support more sources of import ?
      _ -> edhSimpleDescTx srcVal $ \ !badDesc ->
        throwEdhTx EvalError $
          "don't know how to import it: " <> badDesc

importFromApk ::
  EntityStore -> Object -> ArgsReceiver -> ArgsPack -> STM () -> EdhTx
importFromApk !tgtEnt !reExpObj !argsRcvr !fromApk !done !ets =
  recvEdhArgs ets ctx argsRcvr fromApk $ \ !em -> do
    case edh'ctx'eff'target ctx of
      Nothing -> iopdUpdate (odToList em) tgtEnt -- normal import
      Just _esEffs ->
        -- importing effects
        -- note that nil can not appear as for arg receiving,
        -- so no processing of delete semantics
        iopdUpdate (odToList em) =<< prepareEffStore ets tgtEnt
    case edh'ctx'exp'target ctx of
      Nothing -> pure ()
      -- re-export what's imported
      Just _esExps -> prepareExpStore ets reExpObj $ \ !esExps ->
        -- note that nil can not appear as for arg receiving,
        -- so no processing of delete semantics
        iopdUpdate (odToList em) esExps
    done
  where
    !ctx = edh'context ets

importFromObject ::
  EntityStore -> Object -> ArgsReceiver -> Object -> STM () -> EdhTx
importFromObject !tgtEnt !reExpObj !argsRcvr !fromObj !done !ets =
  iopdEmpty >>= \ !arts -> do
    !supers <- readTVar $ edh'obj'supers fromObj
    -- the reversed order ensures that artifacts from a nearer object overwrite
    -- those from farther objects
    sequence_ $ reverse $ collect1 arts <$> fromObj : supers
    !arts' <- iopdSnapshot arts
    runEdhTx ets $
      importFromApk tgtEnt reExpObj argsRcvr (ArgsPack [] arts') done
  where
    moduClass = edh'module'class $ edh'prog'world $ edh'thread'prog ets

    doBindTo :: Object -> Object -> EdhValue -> EdhValue
    doBindTo !this !that = \case
      EdhProcedure !callable !effOuter ->
        EdhBoundProc callable this that effOuter
      !art -> art

    collect1 :: EntityStore -> Object -> STM ()
    collect1 !arts !obj = case edh'obj'store obj of
      HashStore !hs ->
        let !objCls = edh'obj'class obj
            !binder = if objCls == moduClass then id else doBindTo obj fromObj
         in case edh'obj'store objCls of
              ClassStore !cls -> do
                -- ensure instance artifacts overwrite class artifacts
                collectExp (edh'class'arts cls) binder
                collectExp hs binder
              _ ->
                edhSimpleDesc ets (EdhObject $ edh'obj'class fromObj) $
                  \ !badDesc ->
                    -- note this seems not preventing cps exiting,
                    -- at least we can get an error thrown
                    throwEdh ets EvalError $
                      "bad class for the object to be imported - " <> badDesc
      ClassStore !cls -> collectExp (edh'class'arts cls) id
      HostStore !hsd -> case unwrapHostValue hsd of
        Just (fromScope :: Scope) ->
          let !this = edh'scope'this fromScope
              !that = edh'scope'that fromScope
           in collectExp (edh'scope'entity fromScope) (doBindTo this that)
        Nothing -> case edh'obj'store $ edh'obj'class obj of
          ClassStore !cls ->
            collectExp (edh'class'arts cls) (doBindTo obj fromObj)
          _ ->
            edhSimpleDesc ets (EdhObject $ edh'obj'class fromObj) $ \ !badDesc ->
              -- note this seems not preventing cps exiting,
              -- at least we can get an error thrown
              throwEdh ets EvalError $
                "bad class for the host object to be imported - " <> badDesc
      where
        collectExp :: EntityStore -> (EdhValue -> EdhValue) -> STM ()
        collectExp !esFrom !binder =
          iopdLookup (AttrByName edhExportsMagicName) esFrom >>= \case
            Nothing -> return ()
            Just wrapperVal@(EdhObject !expWrapper) ->
              case edh'obj'store expWrapper of
                HashStore !esExpFrom ->
                  iopdToList esExpFrom
                    >>= \ !expl -> iopdUpdate (transEntries expl []) arts
                _ -> edhSimpleDesc ets wrapperVal $ \ !badDesc ->
                  -- note this seems not preventing cps exiting,
                  -- at least we can get an error thrown
                  throwEdh ets UsageError $ "bad export wrapper - " <> badDesc
            Just !badExplVal -> edhSimpleDesc ets badExplVal $ \ !badDesc ->
              -- note this seems not preventing cps exiting,
              -- at least we can get an error thrown
              throwEdh ets UsageError $ "bad export wrapper - " <> badDesc
          where
            transEntries ::
              [(AttrKey, EdhValue)] ->
              [(AttrKey, EdhValue)] ->
              [(AttrKey, EdhValue)]
            transEntries [] result = reverse result -- maintain order as exp
            transEntries ((!key, !val) : rest) result =
              transEntries rest $ (key, binder val) : result

-- | Import some Edh module
--
-- Note the returned module object may still be under going initialization run
importEdhModule :: Text -> EdhTxExit Object -> EdhTx
importEdhModule !importSpec !exit =
  importEdhModule'' importSpec (\_modu !done _ets -> done) exit

-- | Import some Edh module into specified entity
--
-- Note the returned module object may still be under going initialization run,
-- and the receiving may be performed either synchronously or asynchronously
importEdhModule' ::
  EntityStore ->
  Object ->
  ArgsReceiver ->
  Text ->
  EdhTxExit Object ->
  EdhTx
importEdhModule' !tgtEnt !reExpObj !argsRcvr !importSpec !exit !ets =
  runEdhTx ets $
    importEdhModule''
      importSpec
      -- an exception handler triggered during the import in post load
      -- action may appear executed later than subsequent code of the
      -- import statement, this may be surprising
      (\ !modu !done -> importFromObject tgtEnt reExpObj argsRcvr modu done)
      exit

-- | Import some Edh module and perform the `loadAct` after its fully loaded
--
-- Note the returned module object may still be under going initialization run,
-- and the load action may be performed either synchronously or asynchronously
importEdhModule'' ::
  Text ->
  (Object -> STM () -> EdhTx) ->
  EdhTxExit Object ->
  EdhTx
importEdhModule'' !importSpec !loadAct !impExit !etsImp =
  if edh'in'tx etsImp
    then
      throwEdh
        etsImp
        UsageError
        "you don't import file modules from within a transaction"
    else loadEdhModule $ \case
      -- module already loaded, perform the load action immediately, before
      -- returning the module object
      ModuLoaded !modu ->
        runEdhTx etsImp $ loadAct modu $ exitEdh etsImp impExit modu
      -- import error has been encountered, propagate the error immediately
      ModuFailed !exvImport -> edhThrow etsImp exvImport
      -- enqueue the load action to be performed later, then return the module
      -- object that still under in-progress loading, this is crucial to not get
      -- killed due to deadlock detected by GHC RTS, in case of cyclic import
      ModuLoading !loadScope !postQueue -> do
        -- always perform the post load action on the importing thread,
        -- we've checked above that there is no `ai` tx to break
        --
        -- TODO if the initiating thread has terminated when the importee module
        -- finished loading, the load action will get no chance to be executed,
        -- rendering the importing intent fruitless, which is unexpected.
        -- though this should rarely happen, the race condition seems real.
        modifyTVar' postQueue $
          (:) $ \case
            Left !exvImport -> runEdhTx etsImp $ edhThrowTx exvImport
            Right !modu -> runEdhTx etsImp $ loadAct modu $ return ()
        exitEdh etsImp impExit $ edh'scope'this loadScope
  where
    loadEdhModule :: (ModuSlot -> STM ()) -> STM ()
    loadEdhModule !exit = do
      !moduMap <- readTMVar worldModules
      case Map.lookup (HostModule normalizedSpec) moduMap of
        -- attempt the import specification as host module id first
        Just !moduSlotVar -> readTVar moduSlotVar >>= exit
        -- resolving Edh source files from local filesystem
        Nothing ->
          runEdhTx etsImp $ edhContIO $ importFromFS etsImp normalizedSpec exit
      where
        !world = edh'prog'world $ edh'thread'prog etsImp
        !worldModules = edh'world'modules world

        normalizedSpec = normalizeModuRefSpec importSpec

importFromFS :: EdhThreadState -> Text -> (ModuSlot -> STM ()) -> IO ()
importFromFS !etsImp !normalizedSpec !exit =
  let ?frontFile = "__init__.edh"
      ?fileExt = ".edh"
   in locateSrcFileInFS etsImp normalizedSpec $
        \(!moduName, !moduFile) -> do
          !postLoads <- newTVarIO []
          !exvImport <- newTVarIO $ EdhString "<import failed>"
          let !moduId = EdhModule $ T.pack moduFile
              impCleanup moduMap = atomically $ do
                void $ tryPutTMVar worldModules moduMap
                !exv <- readTVar exvImport
                -- the list will be cleared on success,
                -- no negative impact to always send exv
                readTVar postLoads >>= sequence_ . (<*> pure (Left exv))

          bracket (atomically $ takeTMVar worldModules) impCleanup $
            \ !moduMap ->
              case Map.lookup moduId moduMap of
                Just !moduSlotVar -> atomically $ readTVar moduSlotVar >>= exit
                Nothing -> do
                  (!modu, !loadingScope, !moduSlotVar) <- do
                    -- we are the first importer, resolve correct module name
                    -- allocate a loading slot
                    !modu <- createEdhModule world moduName moduFile
                    atomically $ do
                      !loadingScope <- objectScope modu
                      !moduSlotVar <- newTVar $ ModuLoading loadingScope postLoads
                      -- update into world wide module map
                      putTMVar worldModules $ Map.insert moduId moduSlotVar moduMap
                      return (modu, loadingScope, moduSlotVar)
                  -- try load the module in next transaction
                  !src <- readEdhSrcFile moduFile
                  atomically $
                    edhCatch
                      etsImp
                      (runSrcFileInScope loadingScope moduFile src)
                      ( \_moduResult -> do
                          let !loadedSlot = ModuLoaded modu
                          -- update the world wide map for this just loaded module
                          writeTVar moduSlotVar loadedSlot
                          -- trigger all post load actions
                          -- note they should just enque a proper Edh task to
                          -- their respective initiating thread's task queue, so
                          -- here we care neither about exceptions nor orders
                          swapTVar postLoads []
                            >>= sequence_ . (<*> pure (Right modu))
                          -- return the loaded slot
                          exit loadedSlot
                      )
                      $ \etsThrower !exv _recover !rethrow -> case exv of
                        EdhNil -> rethrow nil -- no error occurred
                        _ -> do
                          writeTVar exvImport exv
                          let !failedSlot = ModuFailed exv
                          writeTVar moduSlotVar failedSlot
                          -- cleanup on loading error
                          !moduMap' <- takeTMVar worldModules
                          case Map.lookup moduId moduMap' of
                            Nothing -> putTMVar worldModules moduMap'
                            Just !moduSlotVar' ->
                              if moduSlotVar' == moduSlotVar
                                then
                                  putTMVar worldModules $
                                    Map.delete
                                      moduId
                                      moduMap'
                                else putTMVar worldModules moduMap'
                          -- rethrow in another tx or above cleanup can cease
                          runEdhTx etsThrower $ edhContSTM $ rethrow exv
  where
    !world = edh'prog'world $ edh'thread'prog etsImp
    !worldModules = edh'world'modules world

locateSrcFileInFS ::
  (?frontFile :: FilePath, ?fileExt :: FilePath) =>
  EdhThreadState ->
  Text ->
  ((ModuleName, FilePath) -> IO ()) ->
  IO ()
locateSrcFileInFS !ets !normalizedSpec !exit =
  locateEdhFile normalizedSpec baseDir >>= \case
    Left !err -> atomically $ throwEdh ets PackageError err
    Right !result -> exit result
  where
    baseDir :: FilePath
    baseDir =
      if "<" `T.isPrefixOf` fromDoc
        then "." -- intrinsic module take pwd as import base
        else takeDirectory $ T.unpack fromDoc
      where
        SrcLoc (SrcDoc fromDoc) _src'span =
          edh'exe'src'loc $ edh'ctx'tip $ edh'context ets

readEdhSrcFile :: FilePath -> IO Text
readEdhSrcFile !edhFile =
  TE.streamDecodeUtf8With lenientDecode <$> B.readFile edhFile >>= \case
    -- TODO warn about decoding problems
    Some !srcText _ _ -> return srcText

runSrcFileInScope ::
  Scope -> FilePath -> Text -> EdhTxExit EdhValue -> EdhTx
runSrcFileInScope !runScope !srcFile !srcText !exit !ets = do
  !tipFrame <- newCallFrame runScope (SrcLoc (SrcDoc srcName) zeroSrcRange)
  let !ctxLoad =
        ctx
          { edh'ctx'tip = tipFrame,
            edh'ctx'stack = edh'ctx'tip ctx : edh'ctx'stack ctx,
            edh'ctx'pure = False,
            edh'ctx'exp'target = Nothing,
            edh'ctx'eff'target = Nothing
          }
      !etsRunModu = ets {edh'context = ctxLoad}
   in runEdhTx etsRunModu $ evalEdh srcName srcText exit
  where
    !ctx = edh'context ets
    !srcName = T.pack srcFile

runStmtsInScope ::
  Scope -> Text -> [StmtSrc] -> EdhTxExit EdhValue -> EdhTx
runStmtsInScope !runScope !srcName !stmts !exit !ets = do
  !tipFrame <- newCallFrame runScope (SrcLoc (SrcDoc srcName) zeroSrcRange)
  let !ctxLoad =
        ctx
          { edh'ctx'tip = tipFrame,
            edh'ctx'stack = edh'ctx'tip ctx : edh'ctx'stack ctx,
            edh'ctx'pure = False,
            edh'ctx'exp'target = Nothing,
            edh'ctx'eff'target = Nothing
          }
      !etsRunModu = ets {edh'context = ctxLoad}
   in runEdhTx etsRunModu $ evalBlock stmts exit
  where
    !ctx = edh'context ets

loadEdhFragment ::
  Text -> EdhTxExit (ModuleName, ModuleFile, Text, [StmtSrc]) -> EdhTx
loadEdhFragment !incSpec !exit !ets =
  runEdhTx ets $ edhContIO loadFrag
  where
    world = edh'prog'world $ edh'thread'prog ets
    worldFrags = edh'world'fragments world
    normalizedSpec = normalizeModuRefSpec incSpec

    loadFrag :: IO ()
    loadFrag =
      let ?frontFile = "__include__.edh"
          ?fileExt = ".iedh"
       in locateSrcFileInFS ets normalizedSpec $
            \(!moduName, !fragFile) -> do
              let !fragId = T.pack fragFile
              !tsFile <- modificationTime <$> getFileStatus fragFile
              Map.lookup fragId <$> readTVarIO worldFrags >>= \case
                Just (CachedFrag !tsCache !srcCode !stmts)
                  | tsCache >= tsFile ->
                    atomically $
                      exitEdh ets exit (moduName, fragId, srcCode, stmts)
                _ -> do
                  !srcCode <- readEdhSrcFile fragFile
                  parseEdh world fragId srcCode >>= \case
                    Left !err -> throwIO err
                    Right (!stmts, _docCmt) -> do
                      atomically $
                        modifyTVar' worldFrags $
                          Map.insert fragId $ CachedFrag tsFile srcCode stmts
                      atomically $
                        exitEdh ets exit (moduName, fragId, srcCode, stmts)

includeEdhFragment :: Text -> EdhTxExit EdhValue -> EdhTx
includeEdhFragment !incSpec !exit !ets = runEdhTx ets $
  loadEdhFragment incSpec $ \(!moduName, !fragId, _srcCode, !stmts) ->
    pushEdhStack $ \ !etsInc -> do
      let incScope = contextScope $ edh'context etsInc
      iopdUpdate
        [ (AttrByName "__name__", EdhString moduName),
          (AttrByName "__file__", EdhString fragId)
        ]
        $ edh'scope'entity incScope
      runEdhTx etsInc $
        runStmtsInScope incScope fragId stmts $
          \ !incResult _ets ->
            exitEdh ets exit $ edhDeCaseWrap incResult

obtainEdhFragment :: Text -> EdhTxExit EdhValue -> EdhTx
obtainEdhFragment !incSpec !exit =
  loadEdhFragment incSpec $ \(_moduName, !fragId, !srcCode, !stmts) !ets -> do
    let ExprSrc src'expr src'span = stmtsExpr stmts
    u <- newRUID'STM
    exitEdh ets exit $
      EdhExpr
        (ExprDefi u src'expr (SrcLoc (SrcDoc fragId) src'span))
        srcCode

intplExprSrc :: EdhThreadState -> ExprSrc -> (ExprSrc -> STM ()) -> STM ()
intplExprSrc !ets (ExprSrc !x !ss) !exit =
  intplExpr ets x $ \ !x' -> exit $ ExprSrc x' ss

intplExpr :: EdhThreadState -> Expr -> (Expr -> STM ()) -> STM ()
intplExpr !ets !x !exit = case x of
  IntplExpr !x' -> runEdhTx ets $
    evalExprSrc x' $ \ !val _ets ->
      exit $ LitExpr $ ValueLiteral val
  ExprWithSrc {} -> exit x
  SymbolExpr {} -> exit x
  LitExpr {} -> exit x
  PrefixExpr !pref !x' ->
    intplExprSrc ets x' $ \ !x'' -> exit $ PrefixExpr pref x''
  VoidExpr !x' -> intplExprSrc ets x' $ \ !x'' -> exit $ VoidExpr x''
  AtoIsoExpr !x' -> intplExprSrc ets x' $ \ !x'' -> exit $ AtoIsoExpr x''
  IfExpr !cond !cons !alt -> intplExprSrc ets cond $ \ !cond' ->
    intplStmtSrc ets cons $ \ !cons' -> case alt of
      Nothing -> exit $ IfExpr cond' cons' Nothing
      Just !altx -> intplStmtSrc ets altx $
        \ !altx' -> exit $ IfExpr cond' cons' $ Just altx'
  CaseExpr !tgt !branches -> intplExprSrc ets tgt $ \ !tgt' ->
    intplExprSrc ets branches $ \ !branches' -> exit $ CaseExpr tgt' branches'
  DictExpr !entries -> seqcontSTM (intplDictEntry ets <$> entries) $
    \ !entries' -> exit $ DictExpr entries'
  ListExpr !es ->
    seqcontSTM (intplExprSrc ets <$> es) $ \ !es' -> exit $ ListExpr es'
  ArgsPackExpr !apkr ->
    intplArgsPacker ets apkr $ \ !apkr' -> exit $ ArgsPackExpr apkr'
  ParenExpr !x' -> intplExprSrc ets x' $ \ !x'' -> exit $ ParenExpr x''
  IncludeExpr !xFrom ->
    intplExprSrc ets xFrom $ \ !xFrom' -> exit $ IncludeExpr xFrom'
  IncExprExpr !xFrom ->
    intplExprSrc ets xFrom $ \ !xFrom' -> exit $ IncExprExpr xFrom'
  ImportExpr !rcvr !xFrom !maybeInto -> intplArgsRcvr ets rcvr $ \ !rcvr' ->
    intplExprSrc ets xFrom $ \ !xFrom' -> case maybeInto of
      Nothing -> exit $ ImportExpr rcvr' xFrom' Nothing
      Just !into -> intplExprSrc ets into $ \ !into' ->
        exit $ ImportExpr rcvr' xFrom' (Just into')
  ExportExpr !xExp ->
    intplExprSrc ets xExp $ \ !xExp' -> exit $ ExportExpr xExp'
  NamespaceExpr !pd !apkr -> intplProcDecl ets pd $ \ !pd' ->
    intplArgsPacker ets apkr $ \ !apkr' -> exit $ NamespaceExpr pd' apkr'
  ClassExpr !pd -> intplProcDecl ets pd $ \ !pd' -> exit $ ClassExpr pd'
  MethodExpr !pd -> intplProcDecl ets pd $ \ !pd' -> exit $ MethodExpr pd'
  GeneratorExpr !pd ->
    intplProcDecl ets pd $ \ !pd' -> exit $ GeneratorExpr pd'
  InterpreterExpr !pd ->
    intplProcDecl ets pd $ \ !pd' -> exit $ InterpreterExpr pd'
  ProducerExpr !pd -> intplProcDecl ets pd $ \ !pd' -> exit $ ProducerExpr pd'
  OpDefiExpr !fixity !prec !sym !pd ->
    intplProcDecl ets pd $ \ !pd' -> exit $ OpDefiExpr fixity prec sym pd'
  OpOvrdExpr !fixity !prec !sym !pd ->
    intplProcDecl ets pd $ \ !pd' -> exit $ OpOvrdExpr fixity prec sym pd'
  BlockExpr !ss ->
    seqcontSTM (intplStmtSrc ets <$> ss) $ \ !ss' -> exit $ BlockExpr ss'
  ScopedBlockExpr !ss ->
    seqcontSTM (intplStmtSrc ets <$> ss) $ \ !ss' -> exit $ ScopedBlockExpr ss'
  YieldExpr !x' -> intplExprSrc ets x' $ \ !x'' -> exit $ YieldExpr x''
  ForExpr !scoped !rcvs !iterExpr !bodyStmt ->
    intplExprSrc ets iterExpr $ \ !iterExpr' ->
      intplStmtSrc ets bodyStmt $ \ !bodyStmt' ->
        exit $ ForExpr scoped rcvs iterExpr' bodyStmt'
  WhileExpr !cond !act -> intplExprSrc ets cond $ \ !cond' ->
    intplStmtSrc ets act $ \ !act' -> exit $ WhileExpr cond' act'
  DoWhileExpr !act !cond -> intplExprSrc ets cond $ \ !cond' ->
    intplStmtSrc ets act $ \ !act' -> exit $ DoWhileExpr act' cond'
  EffExpr !effAddr -> case effAddr of
    Perform addr ->
      intplAttrAddrSrc ets addr $ \ !addr' -> exit $ EffExpr $ Perform addr'
    Behave addr ->
      intplAttrAddrSrc ets addr $ \ !addr' -> exit $ EffExpr $ Behave addr'
    Fallback addr ->
      intplAttrAddrSrc ets addr $ \ !addr' -> exit $ EffExpr $ Fallback addr'
  AttrExpr !addr -> intplAttrRef ets addr $ \ !addr' -> exit $ AttrExpr addr'
  IndexExpr !v !t -> intplExprSrc ets v $
    \ !v' -> intplExprSrc ets t $ \ !t' -> exit $ IndexExpr v' t'
  CallExpr !v (ArgsPacker !args !argsSpan) -> intplExprSrc ets v $ \ !v' ->
    seqcontSTM (intplArgSender ets <$> args) $
      \ !args' -> exit $ CallExpr v' $ ArgsPacker args' argsSpan
  InfixExpr !op !lhe !rhe -> intplExprSrc ets lhe $ \ !lhe' ->
    intplExprSrc ets rhe $ \ !rhe' -> exit $ InfixExpr op lhe' rhe'
  DefaultExpr !maybeApkr !xDefault ->
    intplExprSrc ets xDefault $ \ !xDefault' -> case maybeApkr of
      Nothing -> exit $ DefaultExpr Nothing xDefault'
      Just !apkr -> intplArgsPacker ets apkr $ \ !apkr' ->
        exit $ DefaultExpr (Just apkr') xDefault'

intplArgsPacker ::
  EdhThreadState ->
  ArgsPacker ->
  (ArgsPacker -> STM ()) ->
  STM ()
intplArgsPacker !ets (ArgsPacker !argSenders !apkrSpan) !exit =
  seqcontSTM (intplArgSender ets <$> argSenders) $
    \ !argSenders' -> exit $ ArgsPacker argSenders' apkrSpan

intplProcDecl :: EdhThreadState -> ProcDecl -> (ProcDecl -> STM ()) -> STM ()
intplProcDecl _ets pd@HostDecl {} !exit = exit pd
intplProcDecl !ets (ProcDecl !addr !args !anno !body !loc) !exit =
  intplAttrAddrSrc ets addr $ \ !addr' -> intplArgsRcvr ets args $ \ !args' ->
    intplStmtSrc ets body $ \ !body' ->
      exit $ ProcDecl addr' args' anno body' loc

intplDictEntry ::
  EdhThreadState ->
  (DictKeyExpr, ExprSrc) ->
  ((DictKeyExpr, ExprSrc) -> STM ()) ->
  STM ()
intplDictEntry !ets (k@LitDictKey {}, !x) !exit =
  intplExprSrc ets x $ \ !x' -> exit (k, x')
intplDictEntry !ets (AddrDictKey !k, !x) !exit = intplAttrAddrSrc ets k $
  \ !k' -> intplExprSrc ets x $ \ !x' -> exit (AddrDictKey k', x')
intplDictEntry !ets (ExprDictKey !k, !x) !exit = intplExprSrc ets k $
  \ !k' -> intplExprSrc ets x $ \ !x' -> exit (ExprDictKey k', x')

intplAttrRef :: EdhThreadState -> AttrRef -> (AttrRef -> STM ()) -> STM ()
intplAttrRef !ets !ref !exit = case ref of
  DirectRef !addr -> intplAttrAddrSrc ets addr $ \ !addr' ->
    exit $ DirectRef addr'
  IndirectRef !x' !addr ->
    intplExprSrc ets x' $ \ !x'' -> intplAttrAddrSrc ets addr $ \ !addr' ->
      exit $ IndirectRef x'' addr'
  _ -> exit ref

intplAttrAddrSrc :: EdhThreadState -> AttrAddrSrc -> (AttrAddrSrc -> STM ()) -> STM ()
intplAttrAddrSrc !ets (AttrAddrSrc !addr !src'span) !exit =
  intplAttrAddr ets addr $ \ !addr' -> exit $ AttrAddrSrc addr' src'span

intplAttrAddr :: EdhThreadState -> AttrAddr -> (AttrAddr -> STM ()) -> STM ()
intplAttrAddr !ets (IntplSymAttr src !x) !exit' = runEdhTx ets $
  evalExprSrc x $
    \ !symVal _ets -> case edhUltimate symVal of
      EdhSymbol !sym -> exit' $ LitSymAttr sym
      EdhString !nm -> exit' $ QuaintAttr nm
      _ -> edhSimpleDesc ets symVal $ \ !badDesc ->
        throwEdh ets UsageError $
          "symbol interpolation given unexpected value: "
            <> badDesc
            <> "\n 🔣  evaluated from @( "
            <> src
            <> " )"
intplAttrAddr _ets !addr !exit' = exit' addr

intplArgsRcvr ::
  EdhThreadState -> ArgsReceiver -> (ArgsReceiver -> STM ()) -> STM ()
intplArgsRcvr !ets !a !exit = case a of
  PackReceiver !rcvrs !src'span -> seqcontSTM (intplArgRcvr <$> rcvrs) $
    \ !rcvrs' -> exit $ PackReceiver rcvrs' src'span
  SingleReceiver !rcvr ->
    intplArgRcvr rcvr $ \ !rcvr' -> exit $ SingleReceiver rcvr'
  WildReceiver !src'span -> exit $ WildReceiver src'span
  NullaryReceiver -> exit NullaryReceiver
  where
    intplArgRcvr :: ArgReceiver -> (ArgReceiver -> STM ()) -> STM ()
    intplArgRcvr !a' !exit' = case a' of
      RecvArg !attrAddr !anno !maybeAddr !maybeDefault ->
        intplAttrAddrSrc ets attrAddr $ \ !attrAddr' ->
          case maybeAddr of
            Nothing -> case maybeDefault of
              Nothing -> exit' $ RecvArg attrAddr' anno Nothing Nothing
              Just !x -> intplExprSrc ets x $
                \ !x' -> exit' $ RecvArg attrAddr' anno Nothing $ Just x'
            Just !addr -> intplAttrRef ets addr $ \ !addr' ->
              case maybeDefault of
                Nothing -> exit' $ RecvArg attrAddr' anno (Just addr') Nothing
                Just !x -> intplExprSrc ets x $
                  \ !x' -> exit' $ RecvArg attrAddr' anno (Just addr') $ Just x'
      _ -> exit' a'

intplArgSender :: EdhThreadState -> ArgSender -> (ArgSender -> STM ()) -> STM ()
intplArgSender !ets !a !exit' = case a of
  UnpackPosArgs !v -> intplExprSrc ets v $ \ !v' -> exit' $ UnpackPosArgs v'
  UnpackKwArgs !v -> intplExprSrc ets v $ \ !v' -> exit' $ UnpackKwArgs v'
  UnpackPkArgs !v -> intplExprSrc ets v $ \ !v' -> exit' $ UnpackPkArgs v'
  SendPosArg !v -> intplExprSrc ets v $ \ !v' -> exit' $ SendPosArg v'
  SendKwArg !n !v -> intplAttrAddrSrc ets n $ \ !n' ->
    intplExprSrc ets v $ \ !v' -> exit' $ SendKwArg n' v'

intplStmtSrc :: EdhThreadState -> StmtSrc -> (StmtSrc -> STM ()) -> STM ()
intplStmtSrc !ets (StmtSrc !stmt !sp) !exit' =
  intplStmt ets stmt $ \ !stmt' -> exit' $ StmtSrc stmt' sp

intplStmt :: EdhThreadState -> Stmt -> (Stmt -> STM ()) -> STM ()
intplStmt !ets !stmt !exit = case stmt of
  GoStmt !x -> intplExprSrc ets x $ \ !x' -> exit $ GoStmt x'
  DeferStmt !x -> intplExprSrc ets x $ \ !x' -> exit $ DeferStmt x'
  LetStmt !rcvrs (ArgsPacker !sndrs !sndrsSpan) ->
    intplArgsRcvr ets rcvrs $ \ !rcvrs' ->
      seqcontSTM (intplArgSender ets <$> sndrs) $
        \ !sndrs' -> exit $ LetStmt rcvrs' $ ArgsPacker sndrs' sndrsSpan
  ExtendsStmt !x -> intplExprSrc ets x $ \ !x' -> exit $ ExtendsStmt x'
  PerceiveStmt !sink !body -> intplExprSrc ets sink $ \ !sink' ->
    intplExprSrc ets body $ \ !body' -> exit $ PerceiveStmt sink' body'
  ThrowStmt !x -> intplExprSrc ets x $ \ !x' -> exit $ ThrowStmt x'
  ReturnStmt !x !docCmt -> intplExprSrc ets x $ \ !x' ->
    exit $ ReturnStmt x' docCmt
  ExprStmt !x !docCmt -> intplExpr ets x $ \ !x' -> exit $ ExprStmt x' docCmt
  _ -> exit stmt

resolveUnitSpec :: UnitSpec -> EdhTxExit UnitDefi -> EdhTx
resolveUnitSpec !uomSpec !exit0 !ets = case uomSpec of
  NamedUnit uSym -> resolveNamed uSym $ \uom ->
    exitEdh ets exit0 $ NamedUnitDefi' uom
  ArithUnit nus dus -> resolveArith nus $ \nuds ->
    resolveArith dus $ \duds ->
      exitEdh ets exit0 $ ArithUnitDefi nuds duds
  where
    scope = contextScope $ edh'context ets

    resolveArith ::
      [AttrName] -> ([NamedUnitDefi] -> STM ()) -> STM ()
    resolveArith us = go [] us
      where
        go uds [] exit = exit $ reverse $! uds
        go uds (u : rest) exit = resolveNamed u $ \ud ->
          go (ud : uds) rest exit

    resolveNamed :: AttrName -> (NamedUnitDefi -> STM ()) -> STM ()
    resolveNamed "" exit =
      -- dimensionless unit
      exit $ NamedUnitDefi NoDocCmt True "" []
    resolveNamed uSym exit =
      edhUltimate <$> lookupEdhCtxAttr scope (AttrByName uSym) >>= \case
        EdhUoM (NamedUnitDefi' ud) | uom'defi'sym ud == uSym -> exit ud
        badVal -> edhSimpleDesc ets badVal $ \ !badDesc ->
          throwEdh ets UsageError $
            "expect a UoM by [" <> uSym <> "], but it's a " <> badDesc

-- | Resolve quantity literal to pure number or runtime quantity value
--
-- Bonus support for mathematical notations e.g.
--   3x to be interpreted as 3*x
-- where x is not a UoM but some numeric variable
resolveQuantity ::
  EdhThreadState ->
  Decimal ->
  UnitSpec ->
  (Either Decimal Quantity -> STM ()) ->
  STM ()
resolveQuantity !ets !q !uomSpec !exit0 = case uomSpec of
  NamedUnit uSym -> resolveNamed uSym $ \case
    Left d -> exit0 $ Left $ q * d
    Right uom -> exit0 $ Right $ Quantity q $ NamedUnitDefi' uom
  ArithUnit nus dus -> resolveArith (*) q nus $ \q' nuds ->
    resolveArith (/) q' dus $ \qty duds ->
      exit0 $ Right $ Quantity qty $ ArithUnitDefi nuds duds
  where
    scope = contextScope $ edh'context ets

    resolveArith ::
      (Decimal -> Decimal -> Decimal) ->
      Decimal ->
      [AttrName] ->
      (Decimal -> [NamedUnitDefi] -> STM ()) ->
      STM ()
    resolveArith op q' us = go q' [] us
      where
        go q'' uds [] exit = exit q'' $ reverse $! uds
        go q'' uds (u : rest) exit = resolveNamed u $ \case
          Left d -> go (q'' `op` d) uds rest exit
          Right ud -> go q'' (ud : uds) rest exit

    resolveNamed ::
      AttrName -> (Either Decimal NamedUnitDefi -> STM ()) -> STM ()
    resolveNamed uSym exit =
      edhUltimate <$> lookupEdhCtxAttr scope (AttrByName uSym) >>= \case
        EdhNil ->
          throwEdh ets UsageError $ "UoM [" <> uSym <> "] not in scope"
        EdhDecimal d -> exit $ Left d
        EdhUoM (NamedUnitDefi' ud) | uom'defi'sym ud == uSym -> exit $ Right ud
        badVal -> edhSimpleDesc ets badVal $ \ !badDesc ->
          throwEdh ets UsageError $
            "expect a UoM or pure number by [" <> uSym <> "], but it's a "
              <> badDesc

evalLiteral :: EdhThreadState -> Literal -> (EdhValue -> STM ()) -> STM ()
evalLiteral ets lit exit = case lit of
  DecLiteral !v -> exit (EdhDecimal v)
  StringLiteral !v -> exit (EdhString v)
  BoolLiteral !v -> exit (EdhBool v)
  NilLiteral -> exit nil
  SinkCtor -> EdhSink <$> newSink >>= exit
  ValueLiteral !v -> exit v
  QtyLiteral !q !uomSpec ->
    resolveQuantity ets q (unitSpecWithoutSrc uomSpec) $ \case
      Left d -> exit $ EdhDecimal d
      Right qty -> exit $ EdhQty qty

evalAttrRef :: AttrRef -> EdhTxExit EdhValue -> EdhTx
evalAttrRef !addr !exit !ets = case addr of
  ThisRef {} -> exitEdh ets exit (EdhObject $ edh'scope'this scope)
  ThatRef {} -> exitEdh ets exit (EdhObject $ edh'scope'that scope)
  SuperRef {} -> throwEdh ets UsageError "can not address a single super alone"
  DirectRef (AttrAddrSrc !addr' _) -> resolveEdhAttrAddr ets addr' $ \ !key ->
    lookupEdhCtxAttr scope key >>= \case
      EdhNil ->
        throwEdh ets EvalError $ "not in scope: " <> T.pack (show addr')
      !val -> exitEdh ets exit val
  IndirectRef !tgtExpr (AttrAddrSrc !addr' _) ->
    resolveEdhAttrAddr ets addr' $ \ !key ->
      runEdhTx ets $
        getEdhAttr
          tgtExpr
          key
          ( \ !tgtVal -> case edhUltimate tgtVal of
              EdhObject o ->
                throwEdhTx EvalError $
                  "no such attribute `"
                    <> attrKeyStr key
                    <> "` from a "
                    <> objClassName o
                    <> " object"
              _ -> edhSimpleDescTx tgtVal $ \ !tgtDesc ->
                throwEdhTx EvalError $
                  "no such attribute `"
                    <> attrKeyStr key
                    <> "` from a "
                    <> tgtDesc
          )
          exit
  where
    !ctx = edh'context ets
    !scope = contextScope ctx

evalDictLit ::
  [(DictKeyExpr, ExprSrc)] ->
  [(EdhValue, EdhValue)] ->
  EdhTxExit EdhValue ->
  EdhTx
evalDictLit [] !dsl !exit !ets =
  createEdhDict dsl >>= exitEdh ets exit . EdhDict
-- entry order in DictExpr is reversed as from source, it is reversed again
-- here, so the final dsl here is the same order as in source code
evalDictLit ((k, v) : entries) !dsl !exit !ets = case k of
  LitDictKey !lit -> runEdhTx ets $
    evalExprSrc v $ \ !vVal _ets ->
      evalLiteral ets lit $ \ !kVal ->
        runEdhTx ets $ evalDictLit entries ((kVal, vVal) : dsl) exit
  AddrDictKey !addr -> runEdhTx ets $
    evalAttrRef (DirectRef addr) $ \ !kVal ->
      evalExprSrc v $ \ !vVal -> evalDictLit entries ((kVal, vVal) : dsl) exit
  ExprDictKey !kExpr -> runEdhTx ets $
    evalExprSrc kExpr $ \ !kVal ->
      evalExprSrc v $ \ !vVal -> evalDictLit entries ((kVal, vVal) : dsl) exit

edhSimpleDesc :: EdhThreadState -> EdhValue -> (Text -> STM ()) -> STM ()
edhSimpleDesc !ets !v !exit = edhValueRepr ets v $ \ !valRepr ->
  exit $ case v of
    EdhObject o -> "`" <> objClassName o <> "` object `" <> valRepr <> "`"
    _ -> "'" <> edhTypeNameOf v <> "' value `" <> valRepr <> "`"

edhSimpleDescTx :: EdhValue -> EdhTxExit Text -> EdhTx
edhSimpleDescTx !v !exit !ets =
  edhSimpleDesc ets v $ exitEdh ets exit

edhObjDesc :: EdhThreadState -> Object -> (Text -> STM ()) -> STM ()
edhObjDesc !ets !o = edhObjDesc' ets o odEmpty

edhObjDesc' :: EdhThreadState -> Object -> KwArgs -> (Text -> STM ()) -> STM ()
edhObjDesc' !ets !o !kwargs !exitDesc = runEdhTx ets $
  invokeMagic o (AttrByName "__desc__") (ArgsPack [] kwargs) magicExit $
    \callAsMethod -> \case
      (_, EdhNil) -> case edh'obj'store o of
        ClassStore cls ->
          exitDesc $ "class `" <> procedureName (edh'class'proc cls) <> "`"
        _ -> edhObjRepr ets o $ \ !objRepr ->
          exitDesc $ "`" <> objClassName o <> "` object `" <> objRepr <> "`"
      (_, EdhString !desc) -> exitDesc desc
      !magicArt -> callAsMethod magicArt
  where
    magicExit :: EdhTxExit EdhValue
    magicExit (EdhString r) _ets = exitDesc r
    magicExit reprVal _ets = edhValueStr ets reprVal exitDesc

edhObjDescTx :: Object -> EdhTxExit Text -> EdhTx
edhObjDescTx !o !exitDesc !ets =
  edhObjDesc ets o $ exitEdh ets exitDesc

edhObjDescTx' :: Object -> KwArgs -> EdhTxExit Text -> EdhTx
edhObjDescTx' !o !kwargs !exitDesc !ets =
  edhObjDesc' ets o kwargs $ exitEdh ets exitDesc

edhValueDesc :: EdhThreadState -> EdhValue -> (Text -> STM ()) -> STM ()
edhValueDesc !ets !val !exitDesc = case edhUltimate val of
  EdhObject !o -> edhObjDesc ets o exitDesc
  EdhExpr (ExprDefi _u body loc) src -> do
    let descStr =
          "'Expr' value with AST:\n" <> T.pack (show body)
            <> "\n---expr-defined-at:\n"
            <> prettySrcLoc loc
            <> "\n---expr-source-form:\n"
            <> src
            <> "\n---end-of-expr-desc---"
    exitDesc descStr
  EdhUoM (NamedUnitDefi' (NamedUnitDefi _docCmt isPrim buSym formulae)) -> do
    let showFormula :: (UnitSpec, UnitFormula) -> Text
        showFormula (srcUnit, RatioFormula cFactor) =
          T.pack (show $ numerator r) <> buSym <> " = "
            <> T.pack
              (show (denominator r) <> show srcUnit)
          where
            r = toRational cFactor
        showFormula (_srcUnit, ExprFormula _x !xSrc) =
          "[" <> buSym <> "] = " <> xSrc
    let uCate = if isPrim then "primary" else "secondary"
        descStr =
          "'UoM' value for named " <> uCate <> " unit [" <> buSym
            <> "], with formula(e):\n"
            <> T.unlines (("  " <>) . showFormula <$> formulae)
    exitDesc descStr
  EdhUoM d@(ArithUnitDefi _ns _ds) -> do
    let descStr = T.pack $ "'UoM' value for arithmetic unit [" <> show d <> "]"
    exitDesc descStr
  _ -> edhValueRepr ets val $ \ !valRepr ->
    exitDesc $ "'" <> edhTypeNameOf val <> "' value `" <> valRepr <> "`"

edhValueDescTx :: EdhValue -> EdhTxExit Text -> EdhTx
edhValueDescTx !v !exit !ets =
  edhValueDesc ets v $ exitEdh ets exit

dtcFieldKeys ::
  EdhThreadState -> Object -> ([(AttrKey, Text)] -> STM ()) -> STM ()
dtcFieldKeys !ets !dataCls !exit = case edh'obj'store dataCls of
  ClassStore !cls ->
    dtcFieldKeys'
      ets
      (edh'procedure'args $ edh'procedure'decl $ edh'class'proc cls)
      exit
  _ -> throwEdh ets EvalError "bug: data class not bearing ClassStore"

dtcFieldKeys' ::
  EdhThreadState ->
  ArgsReceiver ->
  ([(AttrKey, Text)] -> STM ()) ->
  STM ()
dtcFieldKeys' !ets !dtcArgRcvrs !exit = case dtcArgRcvrs of
  PackReceiver !drs _ -> go drs []
  SingleReceiver !dr -> go [dr] []
  WildReceiver _ ->
    throwEdh ets UsageError "wild receiver for data class not supported"
  NullaryReceiver ->
    throwEdh ets EvalError "bug: not a data class for dtcFieldKeys"
  where
    go :: [ArgReceiver] -> [(AttrKey, Text)] -> STM ()
    go [] !fs = exit $! reverse fs
    go (dr : rest) !fs = case dr of
      RecvArg _ _ Just {} _ ->
        throwEdh
          ets
          UsageError
          "rename of data class field not supported yet"
      RecvArg (AttrAddrSrc addr _) _ Nothing _ ->
        resolveEdhAttrAddr ets addr $ \ !fk ->
          go rest ((fk, attrKeyStr fk <> "=") : fs)
      RecvRestPkArgs (AttrAddrSrc addr _) _ ->
        resolveEdhAttrAddr ets addr $ \ !fk ->
          go rest ((fk, "***") : fs)
      RecvRestKwArgs (AttrAddrSrc addr _) _ ->
        resolveEdhAttrAddr ets addr $ \ !fk ->
          go rest ((fk, "**") : fs)
      RecvRestPosArgs (AttrAddrSrc addr _) _ ->
        resolveEdhAttrAddr ets addr $ \ !fk ->
          go rest ((fk, "*") : fs)

edhProcessReprs ::
  forall a.
  EdhThreadState ->
  [(EdhValue, Text -> a)] ->
  ([a] -> STM ()) ->
  STM ()
edhProcessReprs !ets !srcList !exit = go srcList []
  where
    go :: [(EdhValue, Text -> a)] -> [a] -> STM ()
    go [] !result = exit $ reverse result
    go ((!v, !p) : rest) !result =
      edhValueRepr ets v $ \ !r -> go rest (p r : result)

escapeString :: Text -> Text
escapeString !txt = T.pack $ ("\"" <>) $ (<> "\"") $ go $ T.unpack txt
  where
    go :: [Char] -> [Char]
    go [] = []
    go (c : rest) = escape c $ go rest

    escape :: Char -> ShowS
    escape !c = case c of
      '\\' -> (++) "\\\\"
      '"' -> (++) "\\\""
      '\n' -> (++) "\\n"
      '\t' -> (++) "\\t"
      '\r' -> (++) "\\r"
      -- todo support more? e.g. \b \g
      _
        | v < 20 -> ("\\u00" <>) . showHex v
        | otherwise -> (c :)
      where
        v = fromEnum c

edhValueRepr :: EdhThreadState -> EdhValue -> (Text -> STM ()) -> STM ()
edhValueRepr !ets !val !exitRepr = case val of
  -- string
  EdhString !txt -> exitRepr $ escapeString txt
  -- range repr
  EdhRange !lower !upper -> edhValueRepr ets (edhBoundValue lower) $
    \ !reprLower -> edhValueRepr ets (edhBoundValue upper) $ \ !reprUpper ->
      exitRepr $
        reprLower <> " " <> edhBoundMarkChar lower <> ".."
          <> edhBoundMarkChar upper
          <> " "
          <> reprUpper
  -- pair repr
  EdhPair !v1 !v2 -> edhValueRepr ets v1 $ \ !repr1 ->
    edhValueRepr ets v2 $ \ !repr2 -> exitRepr $ repr1 <> ":" <> repr2
  -- apk repr
  EdhArgsPack (ArgsPack !args !kwargs) ->
    if null args && odNull kwargs
      then exitRepr "()"
      else edhProcessReprs ets ((\ !v -> (v, id)) <$> args) $ \ !posReprs ->
        edhProcessReprs
          ets
          ( (\(!k, !v) -> (v, \ !r -> attrKeyStr k <> "= " <> r))
              <$> odToList kwargs
          )
          $ \ !kwReprs ->
            exitRepr $
              "( "
                <> T.concat ((<> ", ") <$> (posReprs ++ kwReprs))
                <> ")"
  -- list repr
  EdhList (List _ !ls) ->
    readTVar ls >>= \ !vs ->
      if null vs
        then exitRepr "[]"
        else edhProcessReprs ets ((\ !v -> (v, id)) <$> vs) $ \ !posReprs ->
          exitRepr $ "[ " <> T.concat ((<> ", ") <$> posReprs) <> "]"
  -- dict repr
  EdhDict (Dict !ds) ->
    iopdToReverseList ds >>= \case
      [] -> exitRepr "{}"
      !entries -> reprDictCSR [] entries $
        \ !entriesCSR -> exitRepr $ "{ " <> entriesCSR <> "}"
  -- object repr
  EdhObject !obj -> edhObjRepr ets obj exitRepr
  -- repr of named value is just its name
  EdhNamedValue !n _v -> exitRepr n
  EdhUoM !uom -> exitRepr $ T.pack $ show uom
  EdhQty !qty -> exitRepr $ T.pack $ show qty
  EdhProcedure !callable _ -> exitRepr $ callableName callable
  EdhBoundProc !callable _ _ _ ->
    exitRepr $ "{# bound #} " <> callableName callable
  EdhOrd !ord -> exitRepr $ case ord of
    EQ -> "EQ"
    LT -> "LT"
    GT -> "GT"
  EdhBreak -> exitRepr "{break}"
  EdhContinue -> exitRepr "{continue}"
  EdhFallthrough -> exitRepr "{fallthrough}"
  EdhReturn !rtn -> edhValueRepr ets rtn $ \ !rtnRepr ->
    exitRepr $ "{ return " <> rtnRepr <> " }"
  EdhDefault _ !apk !x _ -> edhValueRepr ets (EdhArgsPack apk) $
    \ !apkRepr -> case x of
      ExprWithSrc _ [SrcSeg src] ->
        exitRepr $ "default " <> apkRepr <> " " <> src
      -- TODO repr of interpolated expr
      _ -> exitRepr $ "<default: " <> apkRepr <> " " <> T.pack (show x) <> ">"
  -- repr of other values, fallback to its 'Show' instance
  _ -> exitRepr $ T.pack $ show val
  where
    -- comma separated repr string for dict entries
    reprDictCSR ::
      [(Text, Text)] -> [(EdhValue, EdhValue)] -> (Text -> STM ()) -> STM ()
    reprDictCSR entries [] !exit' =
      exit' $ T.concat [k <> ": " <> v <> ", " | (k, v) <- entries]
    reprDictCSR entries ((k, v) : rest) exit' = edhValueRepr ets k $ \ !kRepr ->
      do
        let vrDecor :: Text -> Text
            vrDecor = case v of
              -- quote the value repr in the entry if it's a pair
              EdhPair {} -> \r -> "(" <> r <> ")"
              _ -> id
        edhValueRepr ets v $ \ !vRepr ->
          reprDictCSR ((kRepr, vrDecor vRepr) : entries) rest exit'

edhValueReprTx :: EdhValue -> EdhTxExit Text -> EdhTx
edhValueReprTx !val !exit !ets =
  edhValueRepr ets val $ exitEdh ets exit

edhObjReprTx :: Object -> EdhTxExit Text -> EdhTx
edhObjReprTx !o !exit !ets =
  edhObjRepr ets o $ exitEdh ets exit

edhObjStrTx :: Object -> EdhTxExit Text -> EdhTx
edhObjStrTx !o !exit !ets =
  edhObjStr ets o $ exitEdh ets exit

edhObjRepr :: EdhThreadState -> Object -> (Text -> STM ()) -> STM ()
edhObjRepr !ets !o !exitRepr = runEdhTx ets $
  invokeMagic o (AttrByName "__repr__") (ArgsPack [] odEmpty) magicExit $
    \callAsMethod -> \case
      (_, EdhNil) -> exitRepr $ T.pack (show o)
      (_, EdhString !repr) -> exitRepr repr
      !magicArt -> callAsMethod magicArt
  where
    magicExit :: EdhTxExit EdhValue
    magicExit (EdhString r) _ets = exitRepr r
    magicExit v _ets = edhValueRepr ets v exitRepr

edhObjStr :: EdhThreadState -> Object -> (Text -> STM ()) -> STM ()
edhObjStr !ets !o !exitStr = runEdhTx ets $
  invokeMagic o (AttrByName "__str__") (ArgsPack [] odEmpty) magicExit $
    \callAsMethod -> \case
      (_, EdhNil) -> edhObjRepr ets o exitStr -- try use repr
      (_, EdhString !s) -> exitStr s
      !magicArt -> callAsMethod magicArt
  where
    magicExit :: EdhTxExit EdhValue
    magicExit (EdhString s) _ets = exitStr s
    magicExit v _ets = edhValueStr ets v exitStr

edhValueStr :: EdhThreadState -> EdhValue -> (Text -> STM ()) -> STM ()
edhValueStr _ (EdhString !s) !exit = exit s
edhValueStr _ (EdhUUID !u) !exit = exit $ UUID.toText u
edhValueStr ets (EdhObject !o) !exit = edhObjStr ets o exit
edhValueStr _ (EdhNamedValue !name EdhNil) !exit = exit name
edhValueStr !ets (EdhNamedValue _ !v) !exit = edhValueStr ets v exit
edhValueStr _ (EdhUoM !uom) !exit = exit $ T.pack $ show uom
edhValueStr _ (EdhQty !qty) !exit = exit $ T.pack $ show qty
edhValueStr !ets !v !exit = edhValueRepr ets v exit

edhValueStrTx :: EdhValue -> EdhTxExit Text -> EdhTx
edhValueStrTx !v !exit !ets =
  edhValueStr ets v $ exitEdh ets exit

edhValueBlob' ::
  EdhThreadState -> EdhValue -> STM () -> (ByteString -> STM ()) -> STM ()
edhValueBlob' _ (EdhBlob !b) _ !exit = exit b
edhValueBlob' _ (EdhString !str) _ !exit = exit $ TE.encodeUtf8 str
edhValueBlob' !ets (EdhObject !o) naExit !exitBlob = runEdhTx ets $
  invokeMagic o (AttrByName "__blob__") (ArgsPack [] odEmpty) magicExit $
    \callAsMethod -> \case
      (_, EdhNil) -> naExit
      (_, EdhBlob b) -> exitBlob b
      !magicArt -> callAsMethod magicArt
  where
    magicExit :: EdhTxExit EdhValue
    magicExit (EdhBlob b) _ets = exitBlob b
    magicExit v _ets = edhValueBlob' ets v naExit exitBlob
edhValueBlob' _ _ !naExit _ = naExit

edhValueBlobTx' :: EdhValue -> EdhTx -> EdhTxExit ByteString -> EdhTx
edhValueBlobTx' !val !naExit !exit !ets =
  edhValueBlob' ets val (runEdhTx ets naExit) $ exitEdh ets exit

edhValueBlob :: EdhThreadState -> EdhValue -> (ByteString -> STM ()) -> STM ()
edhValueBlob !ets !val =
  edhValueBlob' ets val $
    edhSimpleDesc ets val $ \ !badDesc ->
      throwEdh ets UsageError $ "not convertible to blob: " <> badDesc

edhValueBlobTx :: EdhValue -> EdhTxExit ByteString -> EdhTx
edhValueBlobTx !val !exit !ets = edhValueBlob ets val $ exitEdh ets exit

edhValueJsonTx :: EdhValue -> EdhTxExit Text -> EdhTx
edhValueJsonTx !val !exit !ets = edhValueJson ets val $ exitEdh ets exit

-- | Coercing an Edh value to valid JSON in string form
--
-- *) nil translates to null
-- *) decimal as its repr (todo fractional format and scientific notation)
-- *) `__json__()` magic method from an object is honored
-- *) other value is coerced to a string
--
-- *) a key is always coerced to string
-- *) no trailing comma
-- *)
edhValueJson :: EdhThreadState -> EdhValue -> (Text -> STM ()) -> STM ()
edhValueJson !ets !value !exitJson = valJson value exitJson
  where
    valJson :: EdhValue -> (Text -> STM ()) -> STM ()
    valJson !val !exit = case val of
      EdhString !str -> exit $ strJson str
      -- todo deal with fractional format and scientific notation
      EdhDecimal !d -> exit $ T.pack $ show d
      EdhNil -> exit "null"
      EdhNamedValue _ EdhNil -> exit "null"
      EdhNamedValue "null" _ -> exit "null"
      EdhNamedValue _ !termVal -> valJson termVal exit
      EdhBool True -> exit "true"
      EdhBool False -> exit "false"
      EdhList (List _ !lv) -> readTVar lv >>= flip listJson exit
      EdhDict (Dict !ds) -> iopdToList ds >>= flip dictJson exit
      EdhArgsPack (ArgsPack !args !kwargs) ->
        if null args
          then
            if odNull kwargs
              then exit "[]"
              else kwsJson (odToList kwargs) exit
          else
            if odNull kwargs
              then listJson args exit
              else
                kwsJson
                  ( odToList kwargs
                      ++ zip (AttrByName . T.pack . show <$> [0 :: Int ..]) args
                  )
                  exit
      EdhObject !o -> runEdhTx ets $
        invokeMagic o (AttrByName "__json__") (ArgsPack [] odEmpty) magicExit $
          \callAsMethod -> \case
            (_, EdhNil) -> exit "null"
            (_, EdhString !json) -> exit json
            magicArt@(_, EdhProcedure {}) -> callAsMethod magicArt
            magicArt@(_, EdhBoundProc {}) -> callAsMethod magicArt
            (_, !jsonVal) -> valJson jsonVal exit
      _ -> edhValueRepr ets val $ \case
        "null" -> exit "null"
        _ -> edhValueStr ets val $ exit . strJson
      where
        magicExit :: EdhTxExit EdhValue
        magicExit (EdhString json) _ets = exit json
        magicExit v _ets = valJson v exit

    strJson :: Text -> Text
    strJson = TE.decodeUtf8With lenientDecode . BL.toStrict . A.encode

    listJson :: [EdhValue] -> (Text -> STM ()) -> STM ()
    listJson [] !exit = exit "[]"
    listJson !vs !exit = go [] vs $
      \ !jsons -> exit $ "[ " <> T.intercalate ", " jsons <> " ]"
      where
        go :: [Text] -> [EdhValue] -> ([Text] -> STM ()) -> STM ()
        go !jsons [] !exit' = exit' $ reverse jsons
        go !jsons (v : rest) !exit' =
          valJson v $ \ !json -> go (json : jsons) rest exit'

    dictJson :: [(EdhValue, EdhValue)] -> (Text -> STM ()) -> STM ()
    dictJson [] !exit = exit "{}"
    dictJson !dictEntries !exit = go [] dictEntries $
      \ !reprs -> exit $ "{ " <> T.intercalate ", " reprs <> " }"
      where
        go :: [Text] -> [(EdhValue, EdhValue)] -> ([Text] -> STM ()) -> STM ()
        go !entries [] !exit' = exit' $ reverse entries
        go !entries ((k, v) : rest) !exit' = edhValueStr ets k $ \ !kStr ->
          valJson v $ \ !vJson ->
            go ((strJson kStr <> ": " <> vJson) : entries) rest exit'

    kwsJson :: [(AttrKey, EdhValue)] -> (Text -> STM ()) -> STM ()
    kwsJson [] !exit = exit "{}"
    kwsJson !kwsEntries !exit = go [] kwsEntries $
      \ !reprs -> exit $ "{ " <> T.intercalate ", " reprs <> " }"
      where
        go :: [Text] -> [(AttrKey, EdhValue)] -> ([Text] -> STM ()) -> STM ()
        go !entries [] !exit' = exit' $ reverse entries
        go !entries ((!k, !v) : rest) !exit' = valJson v $ \ !vJson ->
          go ((strJson (attrKeyStr k) <> ": " <> vJson) : entries) rest exit'

defineScopeAttr :: EdhThreadState -> AttrKey -> EdhValue -> STM ()
defineScopeAttr !ets !key !val = when (key /= AttrByName "_") $ do
  case edh'ctx'eff'target ctx of
    Nothing ->
      unless (edh'ctx'pure ctx) $
        iopdInsert key val (edh'scope'entity scope)
    Just !esEffs -> iopdInsert key val esEffs
  case edh'ctx'exp'target ctx of
    Nothing -> pure ()
    Just !esExps -> iopdInsert key val esExps
  where
    !ctx = edh'context ets
    !scope = contextScope ctx

defineEffect :: EdhThreadState -> AttrKey -> EdhValue -> STM ()
defineEffect !ets !key !val =
  iopdInsert key val
    =<< prepareEffStore ets (edh'scope'entity $ contextScope $ edh'context ets)

-- | Evaluate an Edh expression definition
evalExprDefi :: ExprDefi -> EdhTxExit EdhValue -> EdhTx
evalExprDefi (ExprDefi _ !x !src'loc) !exit !ets =
  runEdhTx etsEval $ evalExpr' x NoDocCmt $ edhSwitchState ets . exit
  where
    !ctx = edh'context ets
    !tip = edh'ctx'tip ctx
    !etsEval =
      ets
        { edh'context = ctx {edh'ctx'tip = tip {edh'exe'src'loc = src'loc}}
        }

evalExprSrc :: ExprSrc -> EdhTxExit EdhValue -> EdhTx
evalExprSrc (ExprSrc !expr !ss) !exit !ets =
  runEdhTx (etsMovePC ets ss) $
    evalExpr expr $ edhSwitchState ets . exit

-- | Evaluate an Edh expression
evalExpr :: Expr -> EdhTxExit EdhValue -> EdhTx
evalExpr !x !exit = evalExpr' x NoDocCmt exit

evalExprSrc' :: ExprSrc -> OptDocCmt -> EdhTxExit EdhValue -> EdhTx
evalExprSrc' (ExprSrc !expr !ss) !docCmt !exit !ets =
  runEdhTx (etsMovePC ets ss) $
    evalExpr' expr docCmt $ edhSwitchState ets . exit

evalExpr' :: Expr -> OptDocCmt -> EdhTxExit EdhValue -> EdhTx
evalExpr' IntplExpr {} _docCmt _exit =
  throwEdhTx UsageError "{$ $} interpolation outside expr definition"
evalExpr' (ExprWithSrc (ExprSrc !x !x'span) !sss) !docCmt !exit = \ !ets ->
  intplExpr ets x $ \ !x' -> do
    let intplSrc :: SourceSeg -> (Text -> STM ()) -> STM ()
        intplSrc !ss !exit' = case ss of
          SrcSeg !s -> exit' s
          IntplSeg !sx ->
            runEdhTx ets $
              evalExprSrc' sx docCmt $ \ !val _ets ->
                edhValueRepr ets (edhDeCaseWrap val) $ \ !rs -> exit' rs
        curSrcLoc = edh'exe'src'loc $ edh'ctx'tip $ edh'context ets
    seqcontSTM (intplSrc <$> sss) $ \ !ssl -> do
      !u <- newRUID'STM
      exitEdh ets exit $
        EdhExpr (ExprDefi u x' curSrcLoc {src'range = x'span}) $ T.concat ssl
evalExpr' (LitExpr !lit) _docCmt !exit =
  \ !ets -> evalLiteral ets lit $ exitEdh ets exit
evalExpr' (PrefixExpr PrefixPlus !expr') !docCmt !exit =
  evalExprSrc' expr' docCmt exit
evalExpr' (PrefixExpr PrefixMinus !expr') !docCmt !exit =
  evalExprSrc' expr' docCmt $ \ !val -> case edhDeCaseClose val of
    (EdhDecimal !v) -> exitEdhTx exit (EdhDecimal (- v))
    !v ->
      throwEdhTx EvalError $
        "can not negate a "
          <> edhTypeNameOf v
          <> ": "
          <> T.pack (show v)
          <> " ❌"
evalExpr' (PrefixExpr Not !expr') !docCmt !exit =
  evalExprSrc' expr' docCmt $ \ !val -> case edhDeCaseClose val of
    (EdhBool v) -> exitEdhTx exit (EdhBool $ not v)
    !v ->
      throwEdhTx EvalError $
        "expect bool but got a "
          <> edhTypeNameOf v
          <> ": "
          <> T.pack (show v)
          <> " ❌"
evalExpr' (PrefixExpr Guard !expr') !docCmt !exit = \ !ets -> do
  let !world = edh'prog'world $ edh'thread'prog ets
  (consoleLogger $ edh'world'console world)
    30
    (Just $ prettySrcLoc $ contextSrcLoc $ edh'context ets)
    "standalone guard treated as plain value."
  runEdhTx ets $ evalExprSrc' expr' docCmt exit
evalExpr' (VoidExpr !expr) !docCmt !exit =
  evalExprSrc' expr docCmt $ \case
    EdhReturn EdhNil -> exitEdhTx exit EdhNil
    EdhReturn {} ->
      throwEdhTx UsageError "you don't return sth from within a void block"
    _ -> exitEdhTx exit EdhNil
evalExpr' (AtoIsoExpr !expr) !docCmt !exit = \ !ets ->
  runEdhTx ets {edh'in'tx = True} $ -- ensure in'tx state
  -- a complex expression is better quoted within a pair of parenthesis;
  -- and we strip off only 1 layer of parenthesis here, so in case a pure
  -- context intended, double-parenthesis quoting will work
    evalExprSrc' (deParen1 expr) docCmt $ edhSwitchState ets . exit
evalExpr' (IfExpr !cond !cseq !alt) _docCmt !exit =
  evalExprSrc cond $ \ !val !ets -> edhValueNull ets val $ \case
    False -> runEdhTx ets $ evalStmtSrc cseq exit
    True -> case alt of
      Just !elseClause -> runEdhTx ets $ evalStmtSrc elseClause exit
      _ -> exitEdh ets exit nil
evalExpr' (DictExpr !entries) _docCmt !exit = evalDictLit entries [] exit
evalExpr' (ListExpr !xs) _docCmt !exit = evalExprs xs $ \ !l !ets -> do
  !ll <- newTVar l
  !u <- newRUID'STM
  exitEdh ets exit (EdhList $ List u ll)
evalExpr' (ArgsPackExpr (ArgsPacker !argSenders _)) _docCmt !exit = \ !ets ->
  packEdhArgs ets argSenders $ \ !apk -> exitEdh ets exit $ EdhArgsPack apk
evalExpr' (ParenExpr !x) !docCmt !exit = \ !ets ->
  -- use a pure ctx to eval the expr in parenthesis
  runEdhTx ets {edh'context = (edh'context ets) {edh'ctx'pure = True}} $
    evalExprSrc' x docCmt $
      \ !vip -> edhSwitchState ets $ exitEdhTx exit vip
evalExpr' (BlockExpr !stmts) _docCmt !exit = evalBlock stmts exit
evalExpr' (ScopedBlockExpr !stmts) _docCmt !exit = evalScopedBlock stmts exit
evalExpr' (CaseExpr !tgtExpr !branchesExpr) !docCmt !exit =
  evalExprSrc' tgtExpr docCmt $ \ !tgtVal ->
    evalCaseBranches tgtVal branchesExpr exit
-- yield expr evals to the value of caller's `do` expression
evalExpr' (YieldExpr !yieldExpr) !docCmt !exit =
  evalExprSrc' yieldExpr docCmt $ \ !valToYield !ets ->
    case edh'ctx'genr'caller $ edh'context ets of
      Nothing -> throwEdh ets UsageError "unexpected yield"
      Just !yieldVal -> runEdhTx ets $
        yieldVal (edhDeCaseClose valToYield) $ \case
          -- the @do@ block has an exception thrown but uncaught
          Left (!etsThrower, !exv) ->
            -- propagate the exception to the enclosing generator
            --
            -- note we can actually be encountering the exception occurred from
            -- a descendant thread forked by the thread running the enclosing
            -- generator, @etsThrower@ has the correct task queue, and @ets@
            -- has the correct contextual callstack anyway
            edhThrow etsThrower {edh'context = edh'context ets} exv
          -- no exception occurred in the @do@ block, check its intent
          Right !doResult -> case edhDeCaseClose doResult of
            EdhContinue ->
              -- explicit { continue } is propagated to here,
              -- let the generator see nil in this case
              exitEdh ets exit nil
            EdhBreak ->
              -- for loop is breaking, let the generator `return { break }` here
              -- the generator can intervene the return, that'll be black magic
              exitEdh ets exit $ EdhReturn EdhBreak
            dblRtn@(EdhReturn EdhReturn {}) ->
              -- this must be synthesiszed,
              -- in case do block issued return, the for loop would wrap it as
              -- double return, so as to let the yield expr in the generator
              -- propagate the value returning, as the result of the for loop.
              -- the generator can intervene the return, that'll be black magic
              exitEdh ets exit dblRtn
            EdhReturn {} ->
              -- in case its do block issued a return, the for loop should have
              -- double-wrapped the return, which is handled above
              throwEdh ets EvalError "bug: <return> reached yield"
            !val -> exitEdh ets exit val
evalExpr' (ForExpr !scoped !argsRcvr !iterExpr !bodyStmt) _docCmt !exit =
  \ !ets ->
    edhPrepareForLoop
      ets
      scoped
      argsRcvr
      iterExpr
      bodyStmt
      (const $ return ())
      $ \_iterVal !runLoop -> runEdhTx ets (runLoop exit)
evalExpr' (WhileExpr !cndExpr !bodyStmt) _docCmt !exit = do
  let whileLoop :: EdhTx
      whileLoop = evalExprSrc cndExpr $ \ !cndVal !ets ->
        edhValueNull ets cndVal $ \case
          True -> exitEdh ets exit nil
          False -> runEdhTx ets $
            evalStmtSrc bodyStmt $ \ !blkVal ->
              case edhDeCaseClose blkVal of
                -- early stop of procedure
                rtnVal@EdhReturn {} -> exitEdhTx exit rtnVal
                -- break while loop
                EdhBreak -> exitEdhTx exit nil
                -- continue while loop
                _ -> whileLoop
  whileLoop
evalExpr' (DoWhileExpr !bodyStmt !cndExpr) _docCmt !exit = do
  let doWhile :: EdhTx
      doWhile = evalStmtSrc bodyStmt $ \ !blkVal ->
        case edhDeCaseClose blkVal of
          -- early stop of procedure
          rtnVal@EdhReturn {} -> exitEdhTx exit rtnVal
          -- break while loop
          EdhBreak -> exitEdhTx exit nil
          -- continue while loop
          _ -> evalExprSrc cndExpr $ \ !cndVal !ets ->
            edhValueNull ets cndVal $ \case
              True -> exitEdh ets exit nil
              False -> runEdhTx ets doWhile
  doWhile
evalExpr' (EffExpr !effAddr) _docCmt !exit = \ !ets -> case effAddr of
  Perform (AttrAddrSrc !addr _) -> resolveEdhAttrAddr ets addr $
    \ !effKey -> resolveEdhPerform ets effKey $ exitEdh ets exit
  Behave (AttrAddrSrc !addr _) -> resolveEdhAttrAddr ets addr $
    \ !effKey -> resolveEdhBehave ets effKey $ exitEdh ets exit
  Fallback (AttrAddrSrc !addr _) -> resolveEdhAttrAddr ets addr $
    \ !effKey -> resolveEdhFallback ets effKey $ exitEdh ets exit
evalExpr' (AttrExpr !addr) _docCmt !exit = evalAttrRef addr exit
evalExpr' (CallExpr !calleeExpr (ArgsPacker !argsSndr _)) _docCmt !exit =
  evalExprSrc calleeExpr $ \ !calleeVal !ets ->
    edhPrepareCall ets calleeVal argsSndr $
      \ !mkCall -> runEdhTx ets $ mkCall exit
evalExpr' (IndexExpr !ixExpr !tgtExpr) _docCmt !exit =
  evalExprSrc ixExpr $ \ !ixV ->
    let !ixVal = edhDeCaseWrap ixV
     in evalExprSrc tgtExpr $ \ !tgtV -> case edhDeCaseWrap tgtV of
          -- indexing a dict
          (EdhDict (Dict !d)) -> \ !ets ->
            lookupDictItem ixVal d >>= \case
              Nothing -> exitEdh ets exit nil
              Just !val -> exitEdh ets exit val
          -- indexing an apk
          EdhArgsPack (ArgsPack !args !kwargs) -> case edhUltimate ixVal of
            EdhDecimal !idxNum -> case D.decimalToInteger idxNum of
              Just !i ->
                if i < 0 || i >= fromIntegral (length args)
                  then
                    throwEdhTx UsageError $
                      "apk index out of bounds: "
                        <> T.pack (show i)
                        <> " vs "
                        <> T.pack (show $ length args)
                  else exitEdhTx exit $ args !! fromInteger i
              Nothing ->
                throwEdhTx UsageError $
                  "invalid numeric index to an apk: "
                    <> T.pack (show idxNum)
            EdhString !attrName ->
              exitEdhTx exit $ odLookupDefault EdhNil (AttrByName attrName) kwargs
            EdhSymbol !attrSym ->
              exitEdhTx exit $ odLookupDefault EdhNil (AttrBySym attrSym) kwargs
            !badIdxVal ->
              throwEdhTx UsageError $
                "invalid index to an apk: " <> edhTypeNameOf badIdxVal
          -- indexing an object, by calling its ([]) method with ixVal as the single arg
          EdhObject !obj -> \ !ets ->
            lookupEdhObjAttr obj (AttrByName "([])") >>= \case
              (_, EdhNil) ->
                throwEdh ets EvalError $
                  "no ([]) method from: "
                    <> T.pack
                      (show obj)
              (!this', EdhProcedure (EdhMethod !mth) _) ->
                runEdhTx ets $
                  callEdhMethod
                    this'
                    obj
                    mth
                    (ArgsPack [ixVal] odEmpty)
                    id
                    exit
              (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
                runEdhTx ets $
                  callEdhMethod
                    this
                    that
                    mth
                    (ArgsPack [ixVal] odEmpty)
                    id
                    exit
              (_, !badIndexer) ->
                throwEdh ets EvalError $
                  "malformed index method ([]) on "
                    <> T.pack (show obj)
                    <> " - "
                    <> edhTypeNameOf badIndexer
                    <> ": "
                    <> T.pack (show badIndexer)
          tgtVal ->
            throwEdhTx EvalError $
              "don't know how to index "
                <> edhTypeNameOf tgtVal
                <> ": "
                <> T.pack (show tgtVal)
                <> " with "
                <> edhTypeNameOf ixVal
                <> ": "
                <> T.pack (show ixVal)
evalExpr' (IncludeExpr !srcExpr) _docCmt !exit = evalExprSrc' srcExpr NoDocCmt $
  \ !srcVal -> case edhUltimate srcVal of
    EdhString !srcSpec -> includeEdhFragment srcSpec exit
    _ -> edhValueDescTx srcVal $ \ !badDesc ->
      throwEdhTx EvalError $ "don't know how to include it: " <> badDesc
evalExpr' (IncExprExpr !srcExpr) _docCmt !exit = evalExprSrc' srcExpr NoDocCmt $
  \ !srcVal -> case edhUltimate srcVal of
    EdhString !srcSpec -> obtainEdhFragment srcSpec exit
    _ -> edhValueDescTx srcVal $ \ !badDesc ->
      throwEdhTx EvalError $ "don't know how to include it: " <> badDesc
evalExpr' (ExportExpr !exps) !docCmt !exit = \ !ets ->
  -- always export to current this object's scope, which is possibly a
  -- class object. a method procedure's scope has no way to be imported
  -- from. only objects (usually module or namespace objects) can be
  -- an import source.
  prepareExpStore ets (edh'scope'this $ contextScope $ edh'context ets) $
    \ !esExps ->
      runEdhTx
        ets
          { edh'context = (edh'context ets) {edh'ctx'exp'target = Just esExps}
          }
        $ evalExprSrc' exps docCmt $ edhSwitchState ets . exitEdhTx exit
evalExpr' (ImportExpr !argsRcvr !srcExpr !maybeInto) !docCmt !exit = \ !ets ->
  do
    let !ctx = edh'context ets
        !scope = contextScope ctx

        world = edh'prog'world $ edh'thread'prog ets
        !chkExtImp =
          if edh'scope'proc (edh'world'root world)
            == edh'scope'proc (rootScopeOf scope)
            then \_impSpec doImp -> doImp
            else \_impSpec _doImp -> -- todo finer grained control?
              throwEdhTx
                EvalError
                "external module import prohibited in a sandboxed environment"

    case maybeInto of
      Nothing ->
        runEdhTx ets $
          importInto
            chkExtImp
            (edh'scope'entity scope)
            (edh'scope'this scope)
            argsRcvr
            srcExpr
            exit
      Just !intoExpr ->
        runEdhTx ets $
          evalExprSrc' intoExpr docCmt $ \ !intoVal ->
            case edhUltimate intoVal of
              EdhObject !intoObj -> case edh'obj'store intoObj of
                HashStore !hs ->
                  importInto chkExtImp hs intoObj argsRcvr srcExpr exit
                ClassStore !cls ->
                  importInto
                    chkExtImp
                    (edh'class'arts cls)
                    intoObj
                    argsRcvr
                    srcExpr
                    exit
                HostStore !hsd -> case unwrapHostValue hsd of
                  Just (intoScope :: Scope) ->
                    importInto
                      chkExtImp
                      (edh'scope'entity intoScope)
                      (edh'scope'this intoScope)
                      argsRcvr
                      srcExpr
                      exit
                  Nothing ->
                    throwEdhTx UsageError $
                      "can not import into a host object of class "
                        <> objClassName intoObj
              EdhNil -> exitEdhTx exit nil
              _ ->
                throwEdhTx UsageError $
                  "can only import into an object, not a "
                    <> edhTypeNameOf intoVal
evalExpr' (DefaultExpr !maybeApk exprSrc@(ExprSrc !exprDef _)) _docCmt !exit =
  \ !ets -> do
    let ctx = edh'context ets
    case edh'ctx'eff'target ctx of
      -- a default expr in non-pure context is interpreted as defaulting effects
      -- definition, but not so within pure context (e.g. assignment or return)
      Just _esEffs | not $ edh'ctx'pure ctx -> do
        let withKwargs !kwargs = do
              !esEffDefs <-
                prepareEffStore' (AttrByName edhEffectDefaultsMagicName) ets $
                  edh'scope'entity $ contextScope ctx
              -- no nil can come from kwargs of an apk,
              -- so no processing of delete semantics
              iopdUpdate (odToList kwargs) esEffDefs
              runEdhTx
                ets {edh'context = ctx {edh'ctx'eff'target = Just esEffDefs}}
                $ evalExprSrc (deExprSrc exprSrc) $
                  const $ edhSwitchState ets $ exitEdhTx exit nil
        case maybeApk of
          Nothing -> withKwargs odEmpty
          Just (ArgsPacker !argsSndr _) ->
            packEdhArgs ets argsSndr $ \(ArgsPack !args !kwargs) ->
              if null args
                then withKwargs kwargs
                else
                  throwEdh
                    ets
                    UsageError
                    "you don't pass positional args for `effect default`"
      _ -> do
        !u <- newRUID'STM
        let withApk !apk =
              exitEdh ets exit $ EdhDefault u apk exprDef (Just ets)
        case maybeApk of
          Nothing -> withApk $ ArgsPack [] odEmpty
          Just (ArgsPacker !argsSndr _) -> packEdhArgs ets argsSndr withApk
  where
    deExprSrc :: ExprSrc -> ExprSrc
    deExprSrc (ExprSrc (ExprWithSrc x _) _) = deExprSrc x
    deExprSrc x = x
evalExpr' (InfixExpr !opSymSrc !lhExpr !rhExpr) _docCmt !exit =
  evalInfixSrc opSymSrc lhExpr rhExpr exit
-- defining an Edh class
evalExpr' (ClassExpr HostDecl {}) _ _ =
  throwEdhTx EvalError "bug: eval host class decl"
evalExpr'
  ( ClassExpr
      pd@( ProcDecl
             (AttrAddrSrc !addr _)
             !argsRcvr
             _anno
             (StmtSrc !body'stmt _)
             !proc'loc
           )
    )
  !docCmt
  !exit =
    \ !ets -> resolveEdhAttrAddr ets addr $ \ !name -> do
      let !ctx = edh'context ets
          !scope = contextScope ctx
          !rootScope = edh'world'root $ edh'prog'world $ edh'thread'prog ets
          !nsClass = edh'obj'class $ edh'scope'this rootScope
          !metaClass = edh'obj'class nsClass

      !idCls <- newRUID'STM
      !cs <- iopdEmpty
      !ss <- newTVar []
      !mro <- newTVar []
      let allocatorProc :: ArgsPack -> EdhObjectAllocator
          allocatorProc !apkCtor !exitCtor !etsCtor = case argsRcvr of
            -- a normal class
            NullaryReceiver -> exitCtor . HashStore =<< iopdEmpty
            -- a data class
            _ -> recvEdhArgs etsCtor ctx argsRcvr apkCtor $ \ !dataAttrs ->
              dtcFieldKeys' ets argsRcvr $ \ !fks -> do
                let dataFields = odFromList $
                      (<$> fks) $ \(fk, _prefix) ->
                        (fk, odLookupDefault edhNA fk dataAttrs)
                exitCtor $
                  HostStore $
                    wrapHostValue $ ArgsPack [EdhObject clsObj] dataFields

          !clsProc =
            ProcDefi
              { edh'procedure'ident = idCls,
                edh'procedure'name = name,
                edh'procedure'lexi = scope,
                edh'procedure'doc = docCmt,
                edh'procedure'decl = pd
              }
          !cls = Class clsProc cs allocatorProc mro
          !clsObj = Object (ClassStore cls) metaClass ss

          doExit _rtn _ets =
            readTVar ss >>= fillClassMRO cls >>= \case
              "" -> do
                defineScopeAttr ets name $ EdhObject clsObj
                exitEdh ets exit $ EdhObject clsObj
              !mroInvalid -> throwEdh ets UsageError mroInvalid

      let !clsScope =
            Scope
              { edh'scope'entity = cs,
                edh'scope'this = clsObj,
                edh'scope'that = clsObj,
                edh'scope'proc = clsProc,
                edh'effects'stack = []
              }
      !tipFrame <- newCallFrame clsScope proc'loc
      let !clsCtx =
            ctx
              { edh'ctx'tip = tipFrame,
                edh'ctx'stack = edh'ctx'tip ctx : edh'ctx'stack ctx,
                edh'ctx'genr'caller = Nothing,
                edh'ctx'match = true,
                edh'ctx'pure = False,
                edh'ctx'exp'target = Nothing,
                edh'ctx'eff'target = Nothing
              }
          !etsCls = ets {edh'context = clsCtx}

      case argsRcvr of
        -- a normal class
        NullaryReceiver -> pure ()
        -- a data class
        _ -> dtcFieldKeys' ets argsRcvr $ \ !fks -> do
          !fldGetters <-
            sequence
              [ (fk,)
                  <$> mkHostProperty' clsScope fk (dtcFieldGetter fk) Nothing
                | (fk, _reprPrefix) <- fks
              ]
          !mths <-
            sequence
              [ (AttrByName nm,) <$> mkHostProc clsScope mc nm hp
                | (mc, nm, hp) <-
                    [ (EdhMethod, "__repr__", (dtcReprProc, NullaryReceiver)),
                      (EdhMethod, "__compare__", (dtcCmpProc, NullaryReceiver))
                    ]
              ]
          iopdUpdate (fldGetters ++ mths) cs
      -- calling the Edh class definition
      runEdhTx etsCls $ evalStmt body'stmt doExit
    where
      dtcFieldGetter :: AttrKey -> EdhHostProc
      dtcFieldGetter !attrKey !mthExit !ets =
        withThisHostObj ets $ \(ArgsPack [_cls] !dataFields) ->
          case odLookup attrKey dataFields of
            Just !fv -> exitEdh ets mthExit fv
            Nothing ->
              throwEdh ets UsageError $
                "no such field `" <> attrKeyStr attrKey <> "` on data object"

      dtcReprProc :: ArgsPack -> EdhHostProc
      dtcReprProc _ !mthExit !ets =
        withThisHostObj ets $ \(ArgsPack [EdhObject !cls] !dataFields) ->
          dtcFieldKeys ets cls $ \ !fks -> do
            let unnamed :: (AttrKey, Text) -> (EdhValue, Text -> Text)
                unnamed (!k, !p) =
                  if "*" `T.isPrefixOf` p
                    then (v, (p <>))
                    else (v, id)
                  where
                    !v = odLookupDefault edhNA k dataFields
                named :: (AttrKey, Text) -> (EdhValue, Text -> Text)
                named (!k, !p) =
                  if "*" `T.isPrefixOf` p
                    then (v, (p <>))
                    else (v, ((attrKeyStr k <> "=") <>))
                  where
                    !v = odLookupDefault edhNA k dataFields
                rp = if length fks < 3 then unnamed else named
            edhProcessReprs ets (rp <$> fks) $ \ !dfTokens ->
              exitEdh ets mthExit $
                EdhString $
                  edhClassName cls
                    <> "("
                    <> T.intercalate ", " dfTokens
                    <> ")"

      dtcCmpProc :: ArgsPack -> EdhHostProc
      dtcCmpProc !apk !mthExit !ets = case apk of
        ArgsPack [EdhObject !objOther] !kwargs | odNull kwargs ->
          withThisHostObj ets $ \(ArgsPack [EdhObject !cls] !dataFields) ->
            resolveEdhInstance cls objOther >>= \case
              Nothing -> exitEdh ets mthExit edhNA
              Just !instOther ->
                withHostInstance ets instOther $
                  \(ArgsPack [EdhObject !clsOther] !dataFieldsOther) ->
                    if clsOther /= cls
                      then exitEdh ets mthExit edhNA
                      else edhCmpKeyedList
                        ets
                        (odToList dataFields)
                        (odToList dataFieldsOther)
                        $ \case
                          Nothing -> exitEdh ets mthExit edhNA
                          Just !conclusion ->
                            exitEdh ets mthExit $ EdhOrd conclusion
        _ -> exitEdh ets mthExit edhNA -- todo interpret kwargs or throw?

-- defining an Edh namespace
evalExpr' (NamespaceExpr HostDecl {} _) _ _ =
  throwEdhTx EvalError "bug: eval host ns decl"
evalExpr'
  ( NamespaceExpr
      pd@( ProcDecl
             (AttrAddrSrc !addr _)
             _args
             _anno
             (StmtSrc !body'stmt _)
             !proc'loc
           )
      (ArgsPacker !argsSndr _)
    )
  !docCmt
  !exit =
    \ !ets -> packEdhArgs ets argsSndr $ \(ArgsPack !args !kwargs) ->
      if not (null args)
        then
          throwEdh
            ets
            UsageError
            "you don't pass positional args to a namespace"
        else resolveEdhAttrAddr ets addr $ \ !nsName -> do
          !nsStore <- iopdFromList $ odToList kwargs
          !nsObj <- edhCreateNsObj ets docCmt pd nsName nsStore
          let !ctx = edh'context ets
              !nsScope =
                Scope
                  { edh'scope'entity = nsStore,
                    edh'scope'this = nsObj,
                    edh'scope'that = nsObj,
                    edh'scope'proc = objClassProc nsObj,
                    edh'effects'stack = []
                  }
          !tipFrame <- newCallFrame nsScope proc'loc
          let !nsCtx =
                ctx
                  { edh'ctx'tip = tipFrame,
                    edh'ctx'stack = edh'ctx'tip ctx : edh'ctx'stack ctx,
                    edh'ctx'genr'caller = Nothing,
                    edh'ctx'match = true,
                    edh'ctx'pure = False,
                    edh'ctx'exp'target = Nothing,
                    edh'ctx'eff'target = Nothing
                  }
              !etsNs = ets {edh'context = nsCtx}
          -- calling the Edh ns definition
          runEdhTx etsNs $
            evalStmt body'stmt $ \_rtn _ets -> do
              defineScopeAttr ets nsName $ EdhObject nsObj
              exitEdh ets exit $ EdhObject nsObj
evalExpr' (MethodExpr HostDecl {}) _ _ =
  throwEdhTx EvalError "bug: eval host method decl"
evalExpr' (MethodExpr pd@(ProcDecl (AttrAddrSrc !addr _) _ _ _ _)) !docCmt !exit =
  \ !ets -> resolveEdhAttrAddr ets addr $ \ !name -> do
    !idProc <- newRUID'STM
    let !mth =
          EdhMethod
            ProcDefi
              { edh'procedure'ident = idProc,
                edh'procedure'name = name,
                edh'procedure'lexi = contextScope $ edh'context ets,
                edh'procedure'doc = docCmt,
                edh'procedure'decl = pd
              }
        !mthVal = EdhProcedure mth Nothing
    defineScopeAttr ets name mthVal
    exitEdh ets exit mthVal
evalExpr' (GeneratorExpr HostDecl {}) _ _ =
  throwEdhTx EvalError "bug: eval host method decl"
evalExpr' (GeneratorExpr pd@(ProcDecl (AttrAddrSrc !addr _) _ _ _ _)) !docCmt !exit =
  \ !ets -> resolveEdhAttrAddr ets addr $ \ !name -> do
    !idProc <- newRUID'STM
    let !mth =
          EdhGnrtor
            ProcDefi
              { edh'procedure'ident = idProc,
                edh'procedure'name = name,
                edh'procedure'lexi = contextScope $ edh'context ets,
                edh'procedure'doc = docCmt,
                edh'procedure'decl = pd
              }
        !mthVal = EdhProcedure mth Nothing
    defineScopeAttr ets name mthVal
    exitEdh ets exit mthVal
evalExpr' (InterpreterExpr HostDecl {}) _ _ =
  throwEdhTx EvalError "bug: eval host method decl"
evalExpr' (InterpreterExpr pd@(ProcDecl (AttrAddrSrc !addr _) _ _ _ _)) !docCmt !exit =
  \ !ets -> resolveEdhAttrAddr ets addr $ \ !name -> do
    !idProc <- newRUID'STM
    let !mth =
          EdhIntrpr
            ProcDefi
              { edh'procedure'ident = idProc,
                edh'procedure'name = name,
                edh'procedure'lexi = contextScope $ edh'context ets,
                edh'procedure'doc = docCmt,
                edh'procedure'decl = pd
              }
        !mthVal = EdhProcedure mth Nothing
    defineScopeAttr ets name mthVal
    exitEdh ets exit mthVal
evalExpr' (ProducerExpr HostDecl {}) _ _ =
  throwEdhTx EvalError "bug: eval host method decl"
evalExpr' (ProducerExpr pd@(ProcDecl (AttrAddrSrc !addr _) _ _ _ _)) !docCmt !exit =
  \ !ets -> resolveEdhAttrAddr ets addr $ \ !name -> do
    !idProc <- newRUID'STM
    let !mth =
          EdhPrducr
            ProcDefi
              { edh'procedure'ident = idProc,
                edh'procedure'name = name,
                edh'procedure'lexi = contextScope $ edh'context ets,
                edh'procedure'doc = docCmt,
                edh'procedure'decl =
                  pd
                    { edh'procedure'args =
                        alwaysWithOutlet $ edh'procedure'args pd
                    }
              }
        !mthVal = EdhProcedure mth Nothing
    defineScopeAttr ets name mthVal
    exitEdh ets exit mthVal
  where
    bypassOutlet :: ArgReceiver
    bypassOutlet =
      RecvArg
        (AttrAddrSrc (NamedAttr "outlet") noSrcRange)
        Nothing
        (Just (DirectRef (AttrAddrSrc (NamedAttr "_") noSrcRange)))
        (Just (ExprSrc (LitExpr SinkCtor) noSrcRange))
    alwaysWithOutlet :: ArgsReceiver -> ArgsReceiver
    alwaysWithOutlet asr@(PackReceiver !ars !src'span) = go ars
      where
        go :: [ArgReceiver] -> ArgsReceiver
        go [] = PackReceiver (bypassOutlet : ars) src'span
        go (RecvArg (AttrAddrSrc (NamedAttr "outlet") _) _ _ _ : _) = asr
        go (_ : ars') = go ars'
    alwaysWithOutlet
      asr@(SingleReceiver (RecvArg (AttrAddrSrc (NamedAttr "outlet") _) _ _ _)) =
        asr
    alwaysWithOutlet (SingleReceiver !sr) =
      PackReceiver [bypassOutlet, sr] $ argReceiverSpan sr
    alwaysWithOutlet wr@WildReceiver {} = wr
    alwaysWithOutlet wr@NullaryReceiver {} = wr
evalExpr'
  (OpDefiExpr !opFixity !opPrec (OpSymSrc !opSym _opSpan) !opProc)
  !docCmt
  !exit =
    defineOperator opFixity opPrec opSym opProc docCmt exit Nothing
evalExpr'
  (OpOvrdExpr !opFixity !opPrec (OpSymSrc !opSym _opSpan) !opProc)
  !docCmt
  !exit =
    \ !ets ->
      let !ctx = edh'context ets
          !scope = contextScope ctx
          withOverridden =
            runEdhTx ets
              . defineOperator opFixity opPrec opSym opProc docCmt exit
       in lookupEdhCtxAttr scope (AttrByName opSym) >>= \case
            EdhNil -> withOverridden Nothing
            op@(EdhProcedure EdhIntrOp {} _) -> withOverridden $ Just op
            op@(EdhProcedure EdhOprtor {} _) -> withOverridden $ Just op
            op@(EdhBoundProc EdhIntrOp {} _ _ _) -> withOverridden $ Just op
            op@(EdhBoundProc EdhOprtor {} _ _ _) -> withOverridden $ Just op
            !opVal -> edhValueDesc ets opVal $ \ !badDesc ->
              throwEdh ets UsageError $
                "overriding an invalid operator: "
                  <> badDesc
evalExpr' (SymbolExpr !attr) _docCmt !exit = \ !ets -> do
  !sym <- EdhSymbol <$> mkSymbol ("@" <> attr)
  defineScopeAttr ets (AttrByName attr) sym
  exitEdh ets exit sym

evalInfix :: OpSymbol -> Expr -> Expr -> EdhHostProc
evalInfix !opSym !lhExpr !rhExpr !exit =
  evalInfixSrc
    (OpSymSrc opSym noSrcRange)
    (ExprSrc lhExpr noSrcRange)
    (ExprSrc rhExpr noSrcRange)
    exit

evalInfix' ::
  OpSymbol ->
  (EdhValue -> EdhValue -> EdhTx) ->
  Expr ->
  Expr ->
  EdhHostProc
evalInfix' !opSym !notApplicable !lhExpr !rhExpr !exit =
  evalInfixSrc'
    (OpSymSrc opSym noSrcRange)
    notApplicable
    (ExprSrc lhExpr noSrcRange)
    (ExprSrc rhExpr noSrcRange)
    exit

evalInfixSrc :: OpSymSrc -> ExprSrc -> ExprSrc -> EdhHostProc
evalInfixSrc op@(OpSymSrc !opSym _opSpan) = evalInfixSrc' op $
  \ !lhVal !rhVal !ets -> edhSimpleDesc ets lhVal $ \ !lhDesc ->
    edhSimpleDesc ets rhVal $ \ !rhDesc ->
      throwEdh ets EvalError $
        "operator ("
          <> opSym
          <> ") not applicable to "
          <> lhDesc
          <> " and "
          <> rhDesc

evalInfixSrc' ::
  OpSymSrc ->
  (EdhValue -> EdhValue -> EdhTx) ->
  ExprSrc ->
  ExprSrc ->
  EdhHostProc
evalInfixSrc'
  (OpSymSrc !opSym _opSpan)
  !notApplicable
  !lhExpr
  !rhExpr
  !exit
  !ets =
    resolveEdhCtxAttr scope (AttrByName opSym) >>= \case
      Nothing ->
        throwEdh ets EvalError $ "no operator (" <> opSym <> ") in scope"
      Just (!opVal, !op'lexi) -> case opVal of
        EdhProcedure !callable _ ->
          callProc (edh'scope'this op'lexi) (edh'scope'that op'lexi) callable
        EdhBoundProc !callable !this !that _ -> callProc this that callable
        _ -> edhValueDesc ets opVal $ \ !badDesc ->
          throwEdh ets EvalError $
            "not callable as operator (" <> opSym <> "): " <> badDesc
    where
      magicName = "(" <> opSym <> ")"
      rhMagicName = "(" <> opSym <> ".)"

      tryMagicMethod :: EdhValue -> EdhValue -> STM () -> STM ()
      tryMagicMethod !lhVal !rhVal !naExit = case edhUltimate lhVal of
        EdhObject !lhObj ->
          lookupEdhObjAttr lhObj (AttrByName magicName) >>= \case
            (_, EdhNil) -> case edhUltimate rhVal of
              EdhObject !rhObj ->
                lookupEdhObjAttr rhObj (AttrByName rhMagicName) >>= \case
                  (_, EdhNil) -> naExit
                  (!this', EdhProcedure (EdhMethod !mth) _) ->
                    runEdhTx ets $
                      callEdhMethod
                        this'
                        rhObj
                        mth
                        (ArgsPack [lhVal] odEmpty)
                        id
                        chkExitMagic
                  (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
                    runEdhTx ets $
                      callEdhMethod
                        this
                        that
                        mth
                        (ArgsPack [lhVal] odEmpty)
                        id
                        chkExitMagic
                  (_, !badMth) -> edhValueDesc ets badMth $ \ !badDesc ->
                    throwEdh ets UsageError $
                      "malformed magic method "
                        <> rhMagicName
                        <> " on "
                        <> objClassName rhObj
                        <> ", "
                        <> badDesc
              _ -> naExit
            (!this', EdhProcedure (EdhMethod !mth) _) ->
              runEdhTx ets $
                callEdhMethod
                  this'
                  lhObj
                  mth
                  (ArgsPack [rhVal] odEmpty)
                  id
                  chkExitMagic
            (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
              runEdhTx ets $
                callEdhMethod
                  this
                  that
                  mth
                  (ArgsPack [rhVal] odEmpty)
                  id
                  chkExitMagic
            (_, !badMth) -> edhValueDesc ets badMth $ \ !badDesc ->
              throwEdh ets UsageError $
                "malformed magic method "
                  <> magicName
                  <> " on "
                  <> objClassName lhObj
                  <> ", "
                  <> badDesc
        _ -> case edhUltimate rhVal of
          EdhObject !rhObj ->
            lookupEdhObjAttr rhObj (AttrByName rhMagicName) >>= \case
              (_, EdhNil) -> naExit
              (!this', EdhProcedure (EdhMethod !mth) _) ->
                runEdhTx ets $
                  callEdhMethod
                    this'
                    rhObj
                    mth
                    (ArgsPack [lhVal] odEmpty)
                    id
                    chkExitMagic
              (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
                runEdhTx ets $
                  callEdhMethod
                    this
                    that
                    mth
                    (ArgsPack [lhVal] odEmpty)
                    id
                    chkExitMagic
              (_, !badMth) -> edhValueDesc ets badMth $ \ !badDesc ->
                throwEdh ets UsageError $
                  "malformed magic method "
                    <> rhMagicName
                    <> " on "
                    <> edhClassName rhObj
                    <> ", "
                    <> badDesc
          _ -> naExit
        where
          chkExitMagic :: EdhTxExit EdhValue
          chkExitMagic !result _ets = case edhUltimate result of
            EdhDefault _ _ !exprDef !etsDef ->
              -- eval default expression with possibly the designated thread state
              runEdhTx (fromMaybe ets etsDef) $
                evalExpr (deExpr' exprDef) $
                  \ !defVal _ets -> case defVal of
                    -- `return default nil` means more defered default,
                    -- that's only possible from an operator, other than
                    -- the magic method we just called
                    EdhNil -> naExit
                    -- exit with original thread state
                    _ -> exitEdh ets exit defVal
            _ -> exitEdh ets exit result

      tryMagicWithDefault :: ArgsPack -> Expr -> Maybe EdhThreadState -> STM ()
      tryMagicWithDefault !apkDef !exprDef !etsDef = case apkDef of
        ArgsPack [!lhVal, !rhVal] !kwargs
          | odNull kwargs -> tryMagicWithDefault' exprDef etsDef lhVal rhVal
        ArgsPack [] !kwargs -> evalAsNecessary kwargs $ \ !lhVal !rhVal ->
          tryMagicWithDefault' exprDef etsDef lhVal rhVal
        _ -> edhValueDesc ets (EdhArgsPack apkDef) $ \ !apkDesc ->
          throwEdh ets UsageError $ "unexpected apk for default: " <> apkDesc
        where
          evalAsNecessary :: KwArgs -> (EdhValue -> EdhValue -> STM ()) -> STM ()
          evalAsNecessary !kwargs !withVals =
            case odLookup (AttrByName "lhv") kwargs of
              Just !lhVal -> withLHS lhVal
              Nothing -> runEdhTx ets $
                evalExprSrc lhExpr $ \ !lhVal _ets -> withLHS lhVal
            where
              withLHS :: EdhValue -> STM ()
              withLHS !lhVal = case odLookup (AttrByName "rhv") kwargs of
                Just !rhVal -> withVals lhVal rhVal
                Nothing -> runEdhTx ets $
                  evalExprSrc rhExpr $ \ !rhVal _ets ->
                    withVals lhVal rhVal

      tryMagicWithDefault' ::
        Expr -> Maybe EdhThreadState -> EdhValue -> EdhValue -> STM ()
      tryMagicWithDefault' !exprDef !etsDef !lhVal !rhVal =
        tryMagicMethod lhVal rhVal $
          -- eval default expression with possibly the designated thread state
          runEdhTx (fromMaybe ets etsDef) $
            evalExpr (deExpr' exprDef) $
              \ !resultDef _ets -> case resultDef of
                EdhNil -> runEdhTx ets $ notApplicable lhVal rhVal
                -- exit with original thread state
                _ -> exitEdh ets exit resultDef

      callProc :: Object -> Object -> EdhProcDefi -> STM ()
      callProc !this !that !callable = case callable of
        -- calling an intrinsic operator
        EdhIntrOp _ _ (IntrinOpDefi _ _ iop'proc) ->
          runEdhTx ets $
            iop'proc lhExpr rhExpr $ \ !rtnVal _ets ->
              case rtnVal of
                EdhReturn (EdhReturn !rtnVal') ->
                  -- cease defaulting semantics w.r.t. the sacred return
                  -- exit with original thread state
                  exitEdh ets exit rtnVal'
                _ -> case edhUltimate rtnVal of
                  EdhDefault _ !apkDef !exprDef !etsDef ->
                    tryMagicWithDefault apkDef (deExpr' exprDef) etsDef
                  _ ->
                    -- exit with original thread state
                    exitEdh ets exit rtnVal
        -- calling an operator procedure
        EdhOprtor _ _ !op'pred !op'proc ->
          case edh'procedure'args $ edh'procedure'decl op'proc of
            -- 2 pos-args - simple lh/rh value receiving operator
            (PackReceiver [RecvArg {}, RecvArg {}] _) ->
              runEdhTx ets $
                evalExprSrc lhExpr $ \ !lhVal ->
                  evalExprSrc rhExpr $ \ !rhVal ->
                    callEdhOperator
                      this
                      that
                      op'proc
                      op'pred
                      [edhDeCaseClose lhVal, edhDeCaseClose rhVal]
                      $ \ !rtnVal _ets -> case rtnVal of
                        EdhReturn (EdhReturn !rtnVal') ->
                          -- cease defaulting semantics w.r.t. the sacred return
                          -- exit with original thread state
                          exitEdh ets exit rtnVal'
                        _ -> case edhUltimate rtnVal of
                          EdhDefault _ _apkDef !exprDef !etsDef ->
                            tryMagicWithDefault'
                              (deExpr' exprDef)
                              etsDef
                              lhVal
                              rhVal
                          _ ->
                            -- exit with original thread state
                            exitEdh ets exit rtnVal
            -- @remind 3 pos-args - caller scope + lh/rh expr receiving operator
            (PackReceiver [RecvArg {}, RecvArg {}, RecvArg {}] _) -> do
              !lhu <- newRUID'STM
              !rhu <- newRUID'STM
              !scopeWrapper <- mkScopeWrapper ets scope
              runEdhTx ets $
                callEdhOperator
                  this
                  that
                  op'proc
                  op'pred
                  [ EdhObject scopeWrapper,
                    edhExpr lhu lhExpr "",
                    edhExpr rhu rhExpr ""
                  ]
                  $ \ !rtnVal _ets -> case rtnVal of
                    EdhReturn (EdhReturn !rtnVal') ->
                      -- cease defaulting semantics w.r.t. the sacred return
                      -- exit with original thread state
                      exitEdh ets exit rtnVal'
                    _ -> case edhUltimate rtnVal of
                      EdhDefault _ !apkDef !exprDef !etsDef ->
                        tryMagicWithDefault apkDef (deExpr' exprDef) etsDef
                      _ ->
                        -- exit with original thread state
                        exitEdh ets exit rtnVal
            _ ->
              throwEdh ets UsageError $
                "invalid operator signature: "
                  <> T.pack
                    (show $ edh'procedure'args $ edh'procedure'decl op'proc)
        _ ->
          throwEdh ets UsageError $
            "invalid operator: " <> T.pack (show callable)

      edhExpr !u (ExprSrc !x !x'span) !s =
        EdhExpr (ExprDefi u x curSrcLoc {src'range = x'span}) s
      curSrcLoc = edh'exe'src'loc $ edh'ctx'tip ctx

      !ctx = edh'context ets
      !scope = contextScope ctx

defineOperator ::
  OpFixity ->
  Precedence ->
  OpSymbol ->
  ProcDecl ->
  OptDocCmt ->
  EdhTxExit EdhValue ->
  Maybe EdhValue ->
  EdhTx
defineOperator
  !opFixity
  !opPrec
  !opSym
  !opProc
  !docCmt
  !exit
  !predecessor
  !ets =
    if isJust $ edh'ctx'eff'target ctx
      then
        throwEdh
          ets
          UsageError
          "unreasonable for an operator to be effectful"
      else case opProc of
        -- todo support re-declaring an existing operator or method as a new
        --      operator, with separate fixity & precedence
        HostDecl {} -> throwEdh ets EvalError "bug: eval host op decl"
        ProcDecl
          _
          (PackReceiver [] _)
          _anno
          ( StmtSrc
              ( ExprStmt
                  (AttrExpr (DirectRef (AttrAddrSrc !refPreExisting _)))
                  NoDocCmt
                )
              _
            )
          _ ->
            resolveEdhAttrAddr ets refPreExisting $ \ !preKey ->
              lookupEdhCtxAttr scope preKey >>= \case
                EdhNil ->
                  throwEdh ets UsageError $
                    "no existing operator or method ("
                      <> attrAddrStr refPreExisting
                      <> ") in scope"
                EdhProcedure (EdhIntrOp _fixity _prec !opDefi) !effOuter ->
                  defineOpVal $
                    EdhProcedure
                      ( EdhIntrOp
                          opFixity
                          opPrec
                          opDefi {intrinsic'op'symbol = opSym}
                      )
                      effOuter
                EdhProcedure
                  (EdhOprtor _fixity _prec _pred !opDefi)
                  !effOuter ->
                    defineOpVal $
                      EdhProcedure
                        ( EdhOprtor
                            opFixity
                            opPrec
                            predecessor
                            opDefi
                              { edh'procedure'name = AttrByName opSym,
                                edh'procedure'doc = docCmt
                              }
                        )
                        effOuter
                EdhBoundProc
                  (EdhIntrOp _fixity _prec !opDefi)
                  !boundThis
                  !boundThat
                  !effOuter ->
                    defineOpVal $
                      EdhBoundProc
                        ( EdhIntrOp
                            opFixity
                            opPrec
                            opDefi {intrinsic'op'symbol = opSym}
                        )
                        boundThis
                        boundThat
                        effOuter
                EdhBoundProc
                  (EdhOprtor _fixity _prec _pred !opDefi)
                  !boundThis
                  !boundThat
                  !effOuter ->
                    defineOpVal $
                      EdhBoundProc
                        ( EdhOprtor
                            opFixity
                            opPrec
                            predecessor
                            opDefi
                              { edh'procedure'name = AttrByName opSym,
                                edh'procedure'doc = docCmt
                              }
                        )
                        boundThis
                        boundThat
                        effOuter
                -- TODO the method/interpreter should have 2/3 args,
                --      validate that
                EdhProcedure (EdhMethod !mthDefi) !effOuter ->
                  defineOpVal $
                    EdhProcedure
                      ( EdhOprtor
                          opFixity
                          opPrec
                          predecessor
                          mthDefi
                            { edh'procedure'name = AttrByName opSym,
                              edh'procedure'doc = docCmt
                            }
                      )
                      effOuter
                EdhProcedure (EdhIntrpr !mthDefi) !effOuter ->
                  defineOpVal $
                    EdhProcedure
                      ( EdhOprtor
                          opFixity
                          opPrec
                          predecessor
                          mthDefi
                            { edh'procedure'name = AttrByName opSym,
                              edh'procedure'doc = docCmt
                            }
                      )
                      effOuter
                EdhBoundProc
                  (EdhMethod !mthDefi)
                  !boundThis
                  !boundThat
                  !effOuter ->
                    defineOpVal $
                      EdhBoundProc
                        ( EdhOprtor
                            opFixity
                            opPrec
                            predecessor
                            mthDefi
                              { edh'procedure'name = AttrByName opSym,
                                edh'procedure'doc = docCmt
                              }
                        )
                        boundThis
                        boundThat
                        effOuter
                EdhBoundProc
                  (EdhIntrpr !mthDefi)
                  !boundThis
                  !boundThat
                  !effOuter ->
                    defineOpVal $
                      EdhBoundProc
                        ( EdhOprtor
                            opFixity
                            opPrec
                            predecessor
                            mthDefi
                              { edh'procedure'name = AttrByName opSym,
                                edh'procedure'doc = docCmt
                              }
                        )
                        boundThis
                        boundThat
                        effOuter
                !val -> edhValueDesc ets val $ \ !badDesc ->
                  throwEdh ets UsageError $
                    "can not re-declare as an operator from a "
                      <> badDesc
        ProcDecl {} -> case edh'procedure'args opProc of
          -- 2 pos-args - simple lh/rh value receiving operator
          ( PackReceiver
              [ RecvArg _lhName _ Nothing Nothing,
                RecvArg _rhName _ Nothing Nothing
                ]
              _
            ) ->
              defineEdhOp
          -- 3 pos-args - caller scope + lh/rh expr receiving operator
          ( PackReceiver
              [ RecvArg _scopeName _ Nothing Nothing,
                RecvArg _lhName _ Nothing Nothing,
                RecvArg _rhName _ Nothing Nothing
                ]
              _
            ) ->
              defineEdhOp
          _ -> throwEdh ets EvalError "invalid operator arguments signature"
    where
      !ctx = edh'context ets
      !scope = contextScope ctx
      defineOpVal !opVal = do
        defineScopeAttr ets (AttrByName opSym) opVal
        exitEdh ets exit opVal
      defineEdhOp = do
        !idProc <- newRUID'STM
        let !op =
              EdhOprtor
                opFixity
                opPrec
                predecessor
                ProcDefi
                  { edh'procedure'ident = idProc,
                    edh'procedure'name = AttrByName opSym,
                    edh'procedure'lexi = scope,
                    edh'procedure'doc = docCmt,
                    edh'procedure'decl = opProc
                  }
        defineOpVal $ EdhProcedure op Nothing

val2DictEntry ::
  EdhThreadState -> EdhValue -> ((EdhValue, EdhValue) -> STM ()) -> STM ()
val2DictEntry _ (EdhPair !k !v) !exit = exit (k, v)
val2DictEntry _ (EdhArgsPack (ArgsPack [!k, !v] !kwargs)) !exit
  | odNull kwargs = exit (k, v)
val2DictEntry !ets !val _ =
  throwEdh ets UsageError $
    "invalid entry for dict " <> edhTypeNameOf val <> ": " <> T.pack (show val)

pvlToDict :: EdhThreadState -> [EdhValue] -> (DictStore -> STM ()) -> STM ()
pvlToDict !ets !pvl !exit = do
  !ds <- iopdEmpty
  let go [] = exit ds
      go (p : rest) = val2DictEntry ets p $ \(!key, !val) -> do
        iopdInsert key val ds
        go rest
  go pvl

pvlToDictEntries ::
  EdhThreadState -> [EdhValue] -> ([(EdhValue, EdhValue)] -> STM ()) -> STM ()
pvlToDictEntries !ets !pvl !exit = do
  let go !entries [] = exit entries
      go !entries (p : rest) =
        val2DictEntry ets p $ \ !entry -> go (entry : entries) rest
  go [] $ reverse pvl

edhValueNull :: EdhThreadState -> EdhValue -> (Bool -> STM ()) -> STM ()
edhValueNull _ EdhNil !exit = exit True
edhValueNull !ets (EdhNamedValue _ v) !exit = edhValueNull ets v exit
edhValueNull _ (EdhUoM _uom) !exit = exit False
edhValueNull _ (EdhQty (Quantity q _uom)) !exit =
  exit $ D.decimalIsNaN q || q == 0
edhValueNull _ (EdhDecimal d) !exit = exit $ D.decimalIsNaN d || d == 0
edhValueNull _ (EdhBool b) !exit = exit $ not b
edhValueNull _ (EdhString s) !exit = exit $ T.null s
edhValueNull _ (EdhSymbol _) !exit = exit False
edhValueNull _ (EdhDict (Dict ds)) !exit = iopdNull ds >>= exit
edhValueNull _ (EdhList (List _ l)) !exit = readTVar l >>= exit . null
edhValueNull _ (EdhArgsPack (ArgsPack args kwargs)) !exit =
  exit $ null args && odNull kwargs
edhValueNull _ (EdhExpr (ExprDefi _ (LitExpr NilLiteral) _) _) !exit =
  exit True
edhValueNull _ (EdhExpr (ExprDefi _ (LitExpr (DecLiteral d)) _) _) !exit =
  exit $ D.decimalIsNaN d || d == 0
edhValueNull _ (EdhExpr (ExprDefi _ (LitExpr (BoolLiteral b)) _) _) !exit =
  exit b
edhValueNull _ (EdhExpr (ExprDefi _ (LitExpr (StringLiteral s)) _) _) !exit =
  exit $ T.null s
edhValueNull !ets (EdhObject !o) !exit = runEdhTx ets $
  invokeMagic o (AttrByName "__null__") (ArgsPack [] odEmpty) magicExit $
    \callAsMethod -> \case
      (_, EdhNil) -> exit False
      (_, EdhBool !b) -> exit b
      !magicArt -> callAsMethod magicArt
  where
    magicExit :: EdhTxExit EdhValue
    magicExit (EdhBool b) _ets = exit b
    magicExit v _ets = edhValueNull ets v $ exit . not
edhValueNull _ _ !exit = exit False

edhValueNullTx :: EdhValue -> EdhTxExit Bool -> EdhTx
edhValueNullTx v !exit !ets = edhValueNull ets v $ runEdhTx ets . exit

edhIdentEqual :: EdhValue -> EdhValue -> STM Bool
edhIdentEqual (EdhNamedValue x'n x'v) (EdhNamedValue y'n y'v) =
  if x'n == y'n
    then edhIdentEqual x'v y'v
    else return False
edhIdentEqual EdhNamedValue {} _ = return False
edhIdentEqual _ EdhNamedValue {} = return False
edhIdentEqual (EdhDecimal (Decimal 0 0 0)) (EdhDecimal (Decimal 0 0 0)) =
  return True
edhIdentEqual
  (EdhQty (Quantity (Decimal 0 0 0) x'uom))
  (EdhQty (Quantity (Decimal 0 0 0) y'uom)) =
    return $ x'uom == y'uom
edhIdentEqual x y = return $ x == y

edhNamelyEqual ::
  EdhThreadState -> EdhValue -> EdhValue -> (Bool -> STM ()) -> STM ()
edhNamelyEqual !ets (EdhNamedValue !x'n !x'v) (EdhNamedValue !y'n !y'v) !exit =
  if x'n /= y'n then exit False else edhNamelyEqual ets x'v y'v exit
edhNamelyEqual _ EdhNamedValue {} _ !exit = exit False
edhNamelyEqual _ _ EdhNamedValue {} !exit = exit False
edhNamelyEqual !ets !x !y !exit =
  -- it's considered namely not equal if can not trivially concluded, i.e.
  -- may need to invoke magic methods or sth.
  edhValueEqual ets x y $ exit . fromMaybe False

-- note __eq__ magic should supply scalar value-equality result, vectorized
-- result should be provided by operator magics such as (==) and (!=)
edhValueEqual ::
  EdhThreadState -> EdhValue -> EdhValue -> (Maybe Bool -> STM ()) -> STM ()
edhValueEqual !ets !lhVal !rhVal !exitEq =
  if lhv == rhv
    then exitEq $ Just True
    else case lhv of
      EdhNil -> exitEq $ Just False
      EdhArgsPack (ArgsPack !lhArgs !lhKwArgs) -> case rhv of
        EdhArgsPack (ArgsPack !rhArgs !rhKwArgs) ->
          edhListEq ets lhArgs rhArgs $ \case
            Just True ->
              edhKeyedListEq ets (odToList lhKwArgs) (odToList rhKwArgs) exitEq
            !maybeConclusion -> exitEq maybeConclusion
        _ -> exitEq $ Just False
      EdhList (List _ lhll) -> case rhv of
        EdhList (List _ rhll) -> do
          !lhl <- readTVar lhll
          !rhl <- readTVar rhll
          edhListEq ets lhl rhl exitEq
        _ -> exitEq $ Just False
      EdhDict (Dict !lhd) -> case rhv of
        EdhDict (Dict !rhd) -> do
          !lhl <- iopdToList lhd
          !rhl <- iopdToList rhd
          -- regenerate the entry lists with HashMap to elide diffs in
          -- entry order
          edhKeyedListEq
            ets
            (Map.toList $ Map.fromList lhl)
            (Map.toList $ Map.fromList rhl)
            exitEq
        _ -> exitEq $ Just False
      EdhObject !lhObj -> case rhv of
        EdhNil -> exitEq $ Just False
        -- try left-hand magic
        _ -> runEdhTx ets $
          invokeMagic
            lhObj
            (AttrByName "__eq__")
            (ArgsPack [rhVal] odEmpty)
            (chkMagicRtn tryRightHandMagic)
            $ \callAsMethod -> \case
              (_, EdhNil) -> tryRightHandMagic
              !magicArt -> callAsMethod magicArt
      EdhQty lhQty@(Quantity lhq lhu) -> case rhv of
        EdhQty rhQty@(Quantity rhq rhu) ->
          runEdhTx ets $
            unifyToUnit
              lhu
              (Right rhQty)
              (\rhq' _ets -> exitEq $ Just $ rhq' == lhq)
              $ unifyToUnit
                rhu
                (Right lhQty)
                (\lhq' _ets -> exitEq $ Just $ lhq' == rhq)
                $ \_ets -> exitEq $ Just False
        EdhDecimal rhNum ->
          runEdhTx ets $
            qtyToPureNumber lhQty $ \case
              Nothing -> \_ets -> exitEq $ Just False
              Just lhNum -> \_ets -> exitEq $ Just $ lhNum == rhNum
        _ -> tryRightHandMagic
      _ -> tryRightHandMagic
  where
    !lhv = edhUltimate lhVal
    !rhv = edhUltimate rhVal

    chkMagicRtn :: STM () -> EdhTxExit EdhValue
    chkMagicRtn !naExit !magicRtn _ets = case edhUltimate magicRtn of
      EdhBool !conclusion -> exitEq $ Just conclusion
      EdhNil -> naExit
      EdhDefault _ _ !exprDef !etsDef ->
        runEdhTx (fromMaybe ets etsDef) $
          evalExpr (deExpr' exprDef) $
            \ !defVal _ets -> case defVal of
              EdhBool !conclusion -> exitEq $ Just conclusion
              EdhNil -> naExit
              !badVal -> edhValueDesc ets badVal $ \ !badDesc ->
                throwEdh ets UsageError $
                  "the __eq__ magic method returned invalid default result: "
                    <> badDesc
      !badVal -> edhValueDesc ets badVal $ \ !badDesc ->
        throwEdh ets UsageError $
          "the __eq__ magic method returned invalid result: " <> badDesc

    -- in case no __eq__ magic draws a conclusion, don't conclude here,
    -- as they may implement (==) and (!=) for vectorized comparison
    tryRightHandMagic :: STM ()
    tryRightHandMagic = case rhv of
      EdhObject !rhObj -> runEdhTx ets $
        invokeMagic
          rhObj
          (AttrByName "__eq__")
          (ArgsPack [lhVal] odEmpty)
          (chkMagicRtn $ exitEq Nothing)
          $ \callAsMethod -> \case
            (_, EdhNil) -> exitEq Nothing
            !magicArt -> callAsMethod magicArt
      EdhQty rhQty -> case lhv of
        EdhDecimal lhNum -> runEdhTx ets $
          qtyToPureNumber rhQty $ \case
            Nothing -> \_ets -> exitEq $ Just False
            Just rhNum -> \_ets -> exitEq $ Just $ lhNum == rhNum
        _ -> exitEq $ Just False
      _ -> exitEq Nothing

edhListEq ::
  EdhThreadState ->
  [EdhValue] ->
  [EdhValue] ->
  (Maybe Bool -> STM ()) ->
  STM ()
edhListEq !ets !l1 !l2 !exit = go l1 l2
  where
    go :: [EdhValue] -> [EdhValue] -> STM ()
    go [] [] = exit $ Just True
    go (_ : _) [] = exit $ Just False
    go [] (_ : _) = exit $ Just False
    go (lhVal' : lhRest) (rhVal' : rhRest) =
      edhValueEqual ets lhVal' rhVal' $ \case
        Just True -> go lhRest rhRest
        !maybeConclusion -> exit maybeConclusion

edhKeyedListEq ::
  forall k.
  Eq k =>
  EdhThreadState ->
  [(k, EdhValue)] ->
  [(k, EdhValue)] ->
  (Maybe Bool -> STM ()) ->
  STM ()
edhKeyedListEq !ets !l1 !l2 !exit = go l1 l2
  where
    go :: [(k, EdhValue)] -> [(k, EdhValue)] -> STM ()
    go [] [] = exit $ Just True
    go (_ : _) [] = exit $ Just False
    go [] (_ : _) = exit $ Just False
    go ((lhKey, lhVal') : lhRest) ((rhKey, rhVal') : rhRest) =
      if lhKey /= rhKey
        then exit $ Just False
        else edhValueEqual ets lhVal' rhVal' $ \case
          Just True -> go lhRest rhRest
          !maybeConclusion -> exit maybeConclusion

edhCmpList ::
  EdhThreadState ->
  [EdhValue] ->
  [EdhValue] ->
  (Maybe Ordering -> STM ()) ->
  STM ()
edhCmpList !ets !l1 !l2 !exit = go l1 l2
  where
    go :: [EdhValue] -> [EdhValue] -> STM ()
    go [] [] = exit $ Just EQ
    go [] (_ : _) = exit $ Just LT
    go (_ : _) [] = exit $ Just GT
    go (lhHead : lhTail) (rhHead : rhTail) =
      edhCompareValue ets lhHead rhHead $ \case
        Nothing -> exit Nothing
        Just EQ -> go lhTail rhTail
        !conclusion -> exit conclusion

edhCmpKeyedList ::
  forall k.
  Eq k =>
  EdhThreadState ->
  [(k, EdhValue)] ->
  [(k, EdhValue)] ->
  (Maybe Ordering -> STM ()) ->
  STM ()
edhCmpKeyedList !ets !l1 !l2 !exit = go l1 l2
  where
    go :: [(k, EdhValue)] -> [(k, EdhValue)] -> STM ()
    go [] [] = exit $ Just EQ
    go [] (_ : _) = exit $ Just LT
    go (_ : _) [] = exit $ Just GT
    go ((lhKey, lhHead) : lhTail) ((rhKey, rhHead) : rhTail) =
      if lhKey /= rhKey
        then exit Nothing
        else edhCompareValue ets lhHead rhHead $ \case
          Nothing -> exit Nothing
          Just EQ -> go lhTail rhTail
          !conclusion -> exit conclusion

cmpMagicKey :: AttrKey
cmpMagicKey = AttrByName "__compare__"

edhCompareValue ::
  EdhThreadState ->
  EdhValue ->
  EdhValue ->
  (Maybe Ordering -> STM ()) ->
  STM ()
edhCompareValue !ets !lhVal !rhVal !exit = case edhUltimate lhVal of
  EdhObject !lhObj -> case edh'obj'store lhObj of
    ClassStore {} ->
      lookupEdhObjAttr (edh'obj'class lhObj) cmpMagicKey
        >>= tryMagic id lhObj rhVal tryRightHandMagic
    _ ->
      lookupEdhObjAttr lhObj cmpMagicKey
        >>= tryMagic id lhObj rhVal tryRightHandMagic
  _ -> tryRightHandMagic
  where
    inverse :: Ordering -> Ordering
    inverse = \case
      EQ -> EQ
      LT -> GT
      GT -> LT

    tryRightHandMagic = case edhUltimate rhVal of
      EdhObject !rhObj -> case edh'obj'store rhObj of
        ClassStore {} ->
          lookupEdhObjAttr (edh'obj'class rhObj) cmpMagicKey
            >>= tryMagic inverse rhObj lhVal noMagic
        _ ->
          lookupEdhObjAttr rhObj cmpMagicKey
            >>= tryMagic inverse rhObj lhVal noMagic
      _ -> noMagic

    tryMagic ::
      (Ordering -> Ordering) ->
      Object ->
      EdhValue ->
      STM () ->
      (Object, EdhValue) ->
      STM ()
    tryMagic !reorder !obj !opponent !naExit = \case
      (_, EdhNil) -> naExit
      (!this', EdhProcedure (EdhMethod !mth) _) ->
        runEdhTx ets $
          callEdhMethod
            this'
            obj
            mth
            (ArgsPack [opponent] odEmpty)
            id
            chkMagicRtn
      (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
        runEdhTx ets $
          callEdhMethod
            this
            that
            mth
            (ArgsPack [opponent] odEmpty)
            id
            chkMagicRtn
      (_, !badCmpMagic) -> edhValueDesc ets badCmpMagic $ \ !badDesc ->
        throwEdh ets UsageError $ "bad __compare__ magic: " <> badDesc
      where
        chkMagicRtn :: EdhTxExit EdhValue
        chkMagicRtn !magicRtn _ets = case edhUltimate magicRtn of
          EdhDefault _ _ !exprDef !etsDef ->
            -- TODO honor its defaulting semantics
            runEdhTx (fromMaybe ets etsDef) $
              evalExpr (deExpr' exprDef) $
                \ !defVal _ets -> chkMagicExit defVal
          _ -> chkMagicExit magicRtn
          where
            chkMagicExit :: EdhValue -> STM ()
            chkMagicExit = \case
              EdhNil -> naExit
              EdhOrd !ord -> exit $ Just $ reorder ord
              _ -> edhValueDesc ets magicRtn $ \ !badDesc ->
                throwEdh ets UsageError $
                  "invalid result from __compare__: "
                    <> badDesc

    noMagic :: STM ()
    noMagic = case edhUltimate lhVal of
      EdhDecimal !lhNum -> case edhUltimate rhVal of
        EdhDecimal !rhNum ->
          if D.decimalIsNaN lhNum || D.decimalIsNaN rhNum
            then exit Nothing
            else exit $ Just $ compare lhNum rhNum
        EdhQty rhQty ->
          runEdhTx ets $
            qtyToPureNumber rhQty $ \case
              Nothing -> \_ets -> exit Nothing
              Just rhNum -> \_ets -> exit $ Just $ compare lhNum rhNum
        _ -> exit Nothing
      EdhQty lhQty@(Quantity lhq lhu) -> case edhUltimate rhVal of
        EdhQty rhQty@(Quantity rhq rhu) ->
          runEdhTx ets $
            unifyToUnit
              lhu
              (Right rhQty)
              (\rhq' _ets -> exit $ Just $ compare lhq rhq')
              $ unifyToUnit
                rhu
                (Right lhQty)
                (\lhq' _ets -> exit $ Just $ compare lhq' rhq)
                $ \_ets -> exit Nothing
        EdhDecimal rhNum ->
          runEdhTx ets $
            qtyToPureNumber lhQty $ \case
              Nothing -> \_ets -> exit Nothing
              Just lhNum -> \_ets -> exit $ Just $ compare lhNum rhNum
        _ -> exit Nothing
      EdhString lhStr -> case edhUltimate rhVal of
        EdhString rhStr -> exit $ Just $ compare lhStr rhStr
        _ -> exit Nothing
      EdhBool lhCnd -> case edhUltimate rhVal of
        EdhBool rhCnd -> exit $ Just $ compare lhCnd rhCnd
        _ -> exit Nothing
      EdhArgsPack (ArgsPack !lhArgs !lhKwArgs) -> case edhUltimate rhVal of
        EdhArgsPack (ArgsPack !rhArgs !rhKwArgs) ->
          edhCmpList ets lhArgs rhArgs $ \case
            Nothing -> exit Nothing
            Just EQ ->
              edhCmpKeyedList ets (odToList lhKwArgs) (odToList rhKwArgs) exit
            !conclusion -> exit conclusion
        _ -> exit Nothing
      _ -> exit Nothing

resolveEdhPerform :: EdhThreadState -> AttrKey -> (EdhValue -> STM ()) -> STM ()
resolveEdhPerform !ets !effKey !exit = resolveEdhPerform' ets effKey $ \case
  Just !effArt -> exit effArt
  Nothing ->
    throwEdh ets UsageError $ "no such effect: " <> T.pack (show effKey)

resolveEdhPerform' ::
  EdhThreadState ->
  AttrKey ->
  (Maybe EdhValue -> STM ()) ->
  STM ()
resolveEdhPerform' !ets !effKey !exit =
  resolveEffectfulAttr ets effKey edhTargetStackForPerform
    >>= \case
      Just (!effArt, _) -> exit $ Just effArt
      Nothing -> exit Nothing
  where
    edhTargetStackForPerform :: [EdhCallFrame]
    edhTargetStackForPerform = case edh'effects'stack scope of
      [] -> edh'ctx'stack ctx
      outerStack -> outerStack
      where
        !ctx = edh'context ets
        !scope = contextScope ctx

resolveEdhBehave :: EdhThreadState -> AttrKey -> (EdhValue -> STM ()) -> STM ()
resolveEdhBehave !ets !effKey !exit = resolveEdhBehave' ets effKey $ \case
  Just !effArt -> exit effArt
  Nothing ->
    throwEdh ets UsageError $ "no such effect: " <> T.pack (show effKey)

resolveEdhBehave' ::
  EdhThreadState ->
  AttrKey ->
  (Maybe EdhValue -> STM ()) ->
  STM ()
resolveEdhBehave' !ets !effKey !exit =
  resolveEffectfulAttr ets effKey edhTargetStackForBehave
    >>= \case
      Just (!effArt, _) -> exit $ Just effArt
      Nothing -> exit Nothing
  where
    edhTargetStackForBehave :: [EdhCallFrame]
    edhTargetStackForBehave = edh'ctx'stack $ edh'context ets

resolveEdhFallback ::
  EdhThreadState -> AttrKey -> (EdhValue -> STM ()) -> STM ()
resolveEdhFallback !ets !effKey !exit = resolveEdhFallback' ets effKey $ \case
  Just !effArt -> exit effArt
  Nothing ->
    throwEdh ets UsageError $ "no such default effect: " <> T.pack (show effKey)

resolveEdhFallback' ::
  EdhThreadState ->
  AttrKey ->
  (Maybe EdhValue -> STM ()) ->
  STM ()
resolveEdhFallback' !ets !effKey !exit =
  resolveEffectfulDefault ets effKey edhTargetStackForFallback
    >>= \case
      Just (!effArt, _) -> exit $ Just effArt
      Nothing -> exit Nothing
  where
    edhTargetStackForFallback :: [EdhCallFrame]
    edhTargetStackForFallback = edh'ctx'stack $ edh'context ets

parseEdhIndex ::
  EdhThreadState -> EdhValue -> (Either ErrMessage EdhIndex -> STM ()) -> STM ()
parseEdhIndex !ets !val !exit = case val of
  -- empty
  EdhArgsPack (ArgsPack [] !kwargs') | odNull kwargs' -> exit $ Right EdhAll
  -- term
  EdhNamedValue "All" _ -> exit $ Right EdhAll
  EdhNamedValue "Any" _ -> exit $ Right EdhAny
  EdhNamedValue _ !termVal -> parseEdhIndex ets termVal exit
  -- range
  EdhRange !lower !upper -> sliceNum (edhBoundValue lower) $ \case
    Left !err -> exit $ Left err
    Right !lowerVal -> sliceNum (edhBoundValue upper) $ \case
      Left !err -> exit $ Left err
      Right !upperVal ->
        case lowerVal of
          Just !start -> case upperVal of
            Just !stop ->
              if stop >= start
                then do
                  -- ascending
                  let !startN = Just $ case lower of
                        OpenBound {} -> start + 1
                        ClosedBound {} -> start
                      !stopN = Just $ case upper of
                        OpenBound {} -> stop
                        ClosedBound {} -> stop + 1
                  exit $ Right $ EdhSlice startN stopN $ Just 1
                else do
                  -- descending
                  let !startN = Just $ case lower of
                        OpenBound {} -> start -1
                        ClosedBound {} -> start
                      !stopN = Just $ case upper of
                        OpenBound {} -> stop
                        ClosedBound {} -> stop -1
                  exit $ Right $ EdhSlice startN stopN $ Just $ -1
            _ ->
              -- assuming ascending
              exit $
                Right $
                  EdhSlice
                    ( Just $ case lower of
                        OpenBound {} -> start + 1
                        ClosedBound {} -> start
                    )
                    Nothing
                    $ Just 1
          _ -> case upperVal of
            Just !stop ->
              -- assuming ascending
              exit $
                Right $
                  EdhSlice
                    Nothing
                    ( Just $ case upper of
                        OpenBound {} -> stop -1
                        ClosedBound {} -> stop
                    )
                    Nothing
            _ -> edhValueDesc ets val $ \ !rngDesc ->
              throwEdh ets UsageError $ "invalid range as index: " <> rngDesc
  -- range pair
  EdhPair (EdhPair !startVal !stopVal) !stepVal -> sliceNum startVal $ \case
    Left !err -> exit $ Left err
    Right !start -> sliceNum stopVal $ \case
      Left !err -> exit $ Left err
      Right !stop -> sliceNum stepVal $ \case
        Left !err -> exit $ Left err
        Right step -> exit $ Right $ EdhSlice start stop step
  EdhPair !startVal !stopVal -> sliceNum startVal $ \case
    Left !err -> exit $ Left err
    Right !start -> sliceNum stopVal $ \case
      Left !err -> exit $ Left err
      Right !stop -> exit $ Right $ EdhSlice start stop Nothing
  -- single
  _ -> sliceNum val $ \case
    Right Nothing -> exit $ Right EdhAll
    Right (Just !i) -> exit $ Right $ EdhIndex i
    Left !err -> exit $ Left err
  where
    sliceNum :: EdhValue -> (Either Text (Maybe Int) -> STM ()) -> STM ()
    sliceNum !val' !exit' = case val' of
      -- number
      EdhDecimal !idxNum -> case D.decimalToInteger idxNum of
        Just !i -> exit' $ Right $ Just $ fromInteger i
        _ ->
          exit' $
            Left $
              "an integer expected as index number but given: "
                <> T.pack (show idxNum)
      -- term
      EdhNamedValue "All" _ -> exit' $ Right Nothing
      EdhNamedValue "Any" _ -> exit' $ Right Nothing
      EdhNamedValue _ !termVal -> sliceNum termVal exit'
      !badIdxNum -> edhValueRepr ets badIdxNum $ \ !badIdxNumRepr ->
        exit' $
          Left $
            "bad index number of "
              <> edhTypeNameOf badIdxNum
              <> ": "
              <> badIdxNumRepr

-- | Schedule an STM action to be performed in current Edh thread, but after
-- current STM tx committed, and after some txs, those possibly already
-- scheduled
--
-- NOTE this happens as part of current STM tx, so the actual action won't be
--      scheduled if any subsequent Edh code within the tx throws without
--      recovered
-- CAVEAT pay special attention in using this, to not break the semantics of
--       `ai` keyword at scripting level
edhContSTM :: STM () -> EdhTx
edhContSTM !actSTM = edhContSTM' (False <$ actSTM)
{-# INLINE edhContSTM #-}

edhContSTM' :: STM Bool -> EdhTx
edhContSTM' !actSTM !ets =
  if edh'in'tx ets
    then throwEdh ets UsageError "ai transaction boundary broken"
    else writeTBQueue (edh'task'queue ets) $ EdhDoSTM ets actSTM
{-# INLINE edhContSTM' #-}

edhContSTM'' :: EdhThreadState -> STM () -> STM ()
edhContSTM'' !ets !actSTM =
  if edh'in'tx ets
    then throwEdh ets UsageError "ai transaction boundary broken"
    else writeTBQueue (edh'task'queue ets) $ EdhDoSTM ets (False <$ actSTM)
{-# INLINE edhContSTM'' #-}

edhContSTM''' :: EdhThreadState -> STM Bool -> STM ()
edhContSTM''' !ets !actSTM =
  if edh'in'tx ets
    then throwEdh ets UsageError "ai transaction boundary broken"
    else writeTBQueue (edh'task'queue ets) $ EdhDoSTM ets actSTM
{-# INLINE edhContSTM''' #-}

-- | Schedule an IO action to be performed in current Edh thread, but after
-- current STM tx committed, and after some txs, those possibly already
-- scheduled.
--
-- NOTE this happens as part of current STM tx, so the actual action won't be
--      scheduled if any subsequent Edh code within the tx throws without
--      recovered
-- CAVEAT pay special attention in using this, to not break the semantics of
--       `ai` keyword at scripting level
edhContIO :: IO () -> EdhTx
edhContIO !actIO = edhContIO' (False <$ actIO)
{-# INLINE edhContIO #-}

edhContIO' :: IO Bool -> EdhTx
edhContIO' !actIO !ets =
  if edh'in'tx ets
    then throwEdh ets UsageError "ai transaction boundary broken"
    else writeTBQueue (edh'task'queue ets) $ EdhDoIO ets actIO
{-# INLINE edhContIO' #-}

edhContIO'' :: EdhThreadState -> IO () -> STM ()
edhContIO'' !ets !actIO =
  if edh'in'tx ets
    then throwEdh ets UsageError "ai transaction boundary broken"
    else writeTBQueue (edh'task'queue ets) $ EdhDoIO ets (False <$ actIO)
{-# INLINE edhContIO'' #-}

edhContIO''' :: EdhThreadState -> IO Bool -> STM ()
edhContIO''' !ets !actIO =
  if edh'in'tx ets
    then throwEdh ets UsageError "ai transaction boundary broken"
    else writeTBQueue (edh'task'queue ets) $ EdhDoIO ets actIO
{-# INLINE edhContIO''' #-}

edhAfterTxSTM :: STM Bool -> EdhTx
edhAfterTxSTM !actSTM = edhAfterTxSTM' (False <$ actSTM)
{-# INLINE edhAfterTxSTM #-}

edhAfterTxSTM' :: STM Bool -> EdhTx
edhAfterTxSTM' !actSTM !ets =
  writeTBQueue (edh'task'queue ets) $ EdhDoSTM ets actSTM
{-# INLINE edhAfterTxSTM' #-}

edhAfterTxIO :: IO Bool -> EdhTx
edhAfterTxIO !actIO = edhAfterTxIO' (False <$ actIO)
{-# INLINE edhAfterTxIO #-}

edhAfterTxIO' :: IO Bool -> EdhTx
edhAfterTxIO' !actIO !ets =
  writeTBQueue (edh'task'queue ets) $ EdhDoIO ets actIO
{-# INLINE edhAfterTxIO' #-}

regulateEdhSlice ::
  EdhThreadState ->
  Int ->
  (Maybe Int, Maybe Int, Maybe Int) ->
  ((Int, Int, Int) -> STM ()) ->
  STM ()
regulateEdhSlice !ets !len (!start, !stop, !step) !exit = case step of
  Nothing -> case start of
    Nothing -> case stop of
      Nothing -> exit (0, len, 1)
      -- (Any:iStop:Any)
      Just !iStop ->
        if iStop < 0
          then
            let iStop' = len + iStop
             in if iStop' < 0
                  then
                    throwEdh ets UsageError $
                      "stop index out of bounds: "
                        <> T.pack (show iStop)
                        <> " vs "
                        <> T.pack (show len)
                  else exit (0, iStop', 1)
          else
            if iStop > len
              then
                throwEdh ets EvalError $
                  "stop index out of bounds: "
                    <> T.pack (show iStop)
                    <> " vs "
                    <> T.pack (show len)
              else exit (0, iStop, 1)
    Just !iStart -> case stop of
      -- (iStart:Any:Any)
      Nothing ->
        if iStart < 0
          then
            let iStart' = len + iStart
             in if iStart' < 0
                  then
                    throwEdh ets UsageError $
                      "start index out of bounds: "
                        <> T.pack (show iStart)
                        <> " vs "
                        <> T.pack (show len)
                  else exit (iStart', len, 1)
          else
            if iStart > len
              then
                throwEdh ets UsageError $
                  "start index out of bounds: "
                    <> T.pack (show iStart)
                    <> " vs "
                    <> T.pack (show len)
              else exit (iStart, len, 1)
      -- (iStart:iStop:Any)
      Just !iStop -> do
        let !iStart' = if iStart < 0 then len + iStart else iStart
            !iStop' = if iStop < 0 then len + iStop else iStop
        if iStart' < 0 || iStart' > len
          then
            throwEdh ets UsageError $
              "start index out of bounds: "
                <> T.pack (show iStart)
                <> " vs "
                <> T.pack (show len)
          else
            if iStop' < 0 || iStop' > len
              then
                throwEdh ets EvalError $
                  "stop index out of bounds: "
                    <> T.pack (show iStop)
                    <> " vs "
                    <> T.pack (show len)
              else
                if iStart' <= iStop'
                  then
                    if iStart' >= len
                      then
                        throwEdh ets UsageError $
                          "start index out of bounds: "
                            <> T.pack (show iStart)
                            <> " vs "
                            <> T.pack (show len)
                      else exit (iStart', iStop', 1)
                  else
                    if iStart' > len
                      then
                        throwEdh ets UsageError $
                          "start index out of bounds: "
                            <> T.pack (show iStart)
                            <> " vs "
                            <> T.pack (show len)
                      else exit (iStart', iStop', -1)
  Just !iStep ->
    if iStep == 0
      then throwEdh ets UsageError "step can not be zero in slice"
      else
        if iStep < 0
          then
            ( case start of
                Nothing -> case stop of
                  -- (Any:Any: -n)
                  Nothing -> exit (len - 1, -1, iStep)
                  -- (Any:iStop: -n)
                  Just !iStop ->
                    if iStop == -1
                      then exit (len - 1, -1, iStep)
                      else do
                        let !iStop' = if iStop < 0 then len + iStop else iStop
                        if iStop' < -1 || iStop' >= len - 1
                          then
                            throwEdh ets EvalError $
                              "backward stop index out of bounds: "
                                <> T.pack (show iStop)
                                <> " vs "
                                <> T.pack (show len)
                          else exit (len - 1, iStop', iStep)
                Just !iStart -> case stop of
                  -- (iStart:Any: -n)
                  Nothing -> do
                    let !iStart' = if iStart < 0 then len + iStart else iStart
                    if iStart' < 0 || iStart' >= len
                      then
                        throwEdh ets UsageError $
                          "backward start index out of bounds: "
                            <> T.pack (show iStart)
                            <> " vs "
                            <> T.pack (show len)
                      else exit (iStart', -1, iStep)

                  -- (iStart:iStop: -n)
                  Just !iStop -> do
                    let !iStart' = if iStart < 0 then len + iStart else iStart
                    if iStart' < 0 || iStart' >= len
                      then
                        throwEdh ets UsageError $
                          "backward start index out of bounds: "
                            <> T.pack (show iStart)
                            <> " vs "
                            <> T.pack (show len)
                      else
                        if iStop == -1
                          then exit (iStart', -1, iStep)
                          else do
                            let !iStop' = if iStop < 0 then len + iStop else iStop
                            if iStop' < -1 || iStop >= len - 1
                              then
                                throwEdh ets EvalError $
                                  "backward stop index out of bounds: "
                                    <> T.pack (show iStop)
                                    <> " vs "
                                    <> T.pack (show len)
                              else
                                if iStart' < iStop'
                                  then
                                    throwEdh ets EvalError $
                                      "can not step backward from "
                                        <> T.pack (show iStart)
                                        <> " to "
                                        <> T.pack (show iStop)
                                  else exit (iStart', iStop', iStep)
            )
          else -- iStep > 0

            ( case start of
                Nothing -> case stop of
                  -- (Any:Any:n)
                  Nothing -> exit (0, len, iStep)
                  -- (Any:iStop:n)
                  Just !iStop -> do
                    let !iStop' = if iStop < 0 then len + iStop else iStop
                    if iStop' < 0 || iStop' > len
                      then
                        throwEdh ets EvalError $
                          "stop index out of bounds: "
                            <> T.pack (show iStop)
                            <> " vs "
                            <> T.pack (show len)
                      else exit (0, iStop', iStep)
                Just !iStart -> case stop of
                  -- (iStart:Any:n)
                  Nothing -> do
                    let !iStart' = if iStart < 0 then len + iStart else iStart
                    if iStart' < 0 || iStart' >= len
                      then
                        throwEdh ets UsageError $
                          "start index out of bounds: "
                            <> T.pack (show iStart)
                            <> " vs "
                            <> T.pack (show len)
                      else exit (iStart', len, iStep)

                  -- (iStart:iStop:n)
                  Just !iStop -> do
                    let !iStart' = if iStart < 0 then len + iStart else iStart
                    let !iStop' = if iStop < 0 then len + iStop else iStop
                    if iStart' < 0 || iStart' > len
                      then
                        throwEdh ets UsageError $
                          "start index out of bounds: "
                            <> T.pack (show iStart)
                            <> " vs "
                            <> T.pack (show len)
                      else
                        if iStop' < 0 || iStop' > len
                          then
                            throwEdh ets EvalError $
                              "stop index out of bounds: "
                                <> T.pack (show iStop)
                                <> " vs "
                                <> T.pack (show len)
                          else
                            if iStart' > iStop'
                              then
                                throwEdh ets EvalError $
                                  "can not step " <> T.pack (show iStep)
                                    <> " from "
                                    <> T.pack (show iStart)
                                    <> " to "
                                    <> T.pack (show iStop)
                              else exit (iStart', iStop', iStep)
            )

postEdhEvent :: Sink -> EdhValue -> EdhTxExit () -> EdhTx
postEdhEvent !sink !val !exit !ets =
  postEvent sink val >>= \case
    True -> exitEdh ets exit ()
    False ->
      if val == EdhNil
        then exitEdh ets exit () -- allow repeated marking of eos
        else throwEdh ets UsageError "attempt to publish into a sink at eos"

-- | Fork a new Edh thread to run the specified event producer, but hold the
-- production until current thread has later started consuming events from the
-- sink returned here.
launchEventProducer :: EdhTxExit Sink -> Sink -> EdhTx -> EdhTx
launchEventProducer
  !exit
  sink@(Sink _ _ _ _ !subc)
  !producerTx
  !etsConsumer =
    readTVar subc >>= \ !subcBefore ->
      if subcBefore < 0
        then throwEdh etsConsumer UsageError "producer outlet already at eos"
        else
          let prodThAct !etsProducer = do
                !subcNow <- readTVar subc
                when (subcNow == subcBefore) retry
                producerTx etsProducer
           in runEdhTx etsConsumer $
                forkEdh id prodThAct $
                  const $
                    exitEdhTx exit sink

mkHostClass' ::
  Scope ->
  AttrName ->
  (ArgsPack -> EdhObjectAllocator) ->
  EntityStore ->
  [Object] ->
  STM Object
mkHostClass' !scope !className !allocator !classStore !superClasses = do
  !idCls <- newRUID'STM
  !ssCls <- newTVar superClasses
  !mroCls <- newTVar []
  let !clsProc =
        ProcDefi
          idCls
          (AttrByName className)
          scope
          NoDocCmt
          (HostDecl fakeHostProc)
      !cls = Class clsProc classStore allocator mroCls
      !clsObj = Object (ClassStore cls) metaClassObj ssCls
  !mroInvalid <- fillClassMRO cls superClasses
  unless (T.null mroInvalid) $
    throwSTM $
      EdhError
        UsageError
        mroInvalid
        (toDyn nil)
        "<mkHostClass>"
  return clsObj
  where
    fakeHostProc :: ArgsPack -> EdhHostProc
    fakeHostProc _ !exit = exitEdhTx exit nil

    !metaClassObj =
      edh'obj'class $ edh'obj'class $ edh'scope'this $ rootScopeOf scope

mkHostClass ::
  Scope ->
  AttrName ->
  (ArgsPack -> EdhObjectAllocator) ->
  [Object] ->
  (Scope -> STM ()) ->
  STM Object
mkHostClass !scope !className !allocator !superClasses !storeMod = do
  !classStore <- iopdEmpty
  !idCls <- newRUID'STM
  !ssCls <- newTVar superClasses
  !mroCls <- newTVar []
  let !clsProc =
        ProcDefi
          idCls
          (AttrByName className)
          scope
          NoDocCmt
          (HostDecl fakeHostProc)
      !cls = Class clsProc classStore allocator mroCls
      !clsObj = Object (ClassStore cls) metaClassObj ssCls
      !clsScope =
        scope
          { edh'scope'entity = classStore,
            edh'scope'this = clsObj,
            edh'scope'that = clsObj,
            edh'scope'proc = clsProc,
            edh'effects'stack = []
          }
  storeMod clsScope
  !mroInvalid <- fillClassMRO cls superClasses
  unless (T.null mroInvalid) $
    throwSTM $
      EdhError
        UsageError
        mroInvalid
        (toDyn nil)
        "<mkHostClass>"
  return clsObj
  where
    fakeHostProc :: ArgsPack -> EdhHostProc
    fakeHostProc _ !exit = exitEdhTx exit nil

    !metaClassObj =
      edh'obj'class $ edh'obj'class $ edh'scope'this $ rootScopeOf scope

-- | make a sandbox scope from a vanilla object
--
-- the sandbox scope's this/that will be a sandbox object based off the original
-- object, the scope procedure's lexcical scope will be the world's sandbox
-- scope.
--
-- the sandbox object will retain the identity of the original object, while its
-- class procedure's lexcical scope will be changed to the world's sandbox scope
-- so as for reflective scopes created from it to have their outer scopes be the
-- world's sandbox scope.
mkObjSandbox :: EdhThreadState -> Object -> (Scope -> STM ()) -> STM ()
mkObjSandbox !ets !obj !exit = case edh'obj'store obj of
  HashStore !hs -> case edh'obj'store clsObj of
    ClassStore !objCls -> do
      let !clsProc = edh'class'proc objCls
          !sbProc = clsProc {edh'procedure'lexi = edh'world'sandbox world}
          !sbObj =
            obj
              { edh'obj'class =
                  clsObj
                    { edh'obj'store =
                        ClassStore
                          objCls
                            { edh'class'proc = sbProc
                            }
                    }
              }
          !sbScope =
            Scope
              { edh'scope'entity = hs,
                edh'scope'this = sbObj,
                edh'scope'that = sbObj,
                edh'scope'proc = sbProc,
                edh'effects'stack = []
              }
      exit sbScope
    _ -> throwEdh ets EvalError "bug: class object not bearing ClassStore"
  _ ->
    throwEdh ets UsageError "can only make sandbox from a vanilla Edh object"
  where
    !world = edh'prog'world $ edh'thread'prog ets
    !clsObj = edh'obj'class obj

-- | make a scope a sandbox
mkScopeSandbox :: EdhThreadState -> Scope -> (Scope -> STM ()) -> STM ()
mkScopeSandbox !ets !origScope !exit =
  exit origScope {edh'scope'proc = sbProc}
  where
    !world = edh'prog'world $ edh'thread'prog ets
    !origProc = edh'scope'proc origScope
    !sbProc = origProc {edh'procedure'lexi = edh'world'sandbox world}

newSandbox :: EdhThreadState -> STM Scope
newSandbox !ets = do
  !u <- newRUID'STM
  !es <- iopdEmpty
  let newSbObj =
        (edh'scope'this sbScope)
          { edh'obj'store = HashStore es
          }
      newSbProc = sbProc {edh'procedure'ident = u}
  return
    sbScope
      { edh'scope'entity = es,
        edh'scope'this = newSbObj,
        edh'scope'that = newSbObj,
        edh'scope'proc = newSbProc
      }
  where
    !world = edh'prog'world $ edh'thread'prog ets
    !sbScope = edh'world'sandbox world
    !sbProc = edh'scope'proc sbScope

runEdhTxInSandbox :: Scope -> EdhHostProc -> EdhTxExit EdhValue -> EdhTx
runEdhTxInSandbox !sandbox !act !exit !ets =
  runEdhInSandbox ets sandbox act exit

runEdhInSandbox ::
  EdhThreadState ->
  Scope ->
  EdhHostProc ->
  EdhTxExit EdhValue ->
  STM ()
runEdhInSandbox !ets !sandbox !act !exit = do
  !tipFrame <- newCallFrame sandbox (SrcLoc (SrcDoc "<sandbox>") zeroSrcRange)
  let !etsSandbox =
        ets
          { edh'context =
              ctxPriv
                { edh'ctx'tip = tipFrame,
                  edh'ctx'stack =
                    edh'ctx'tip ctxPriv :
                    edh'ctx'stack ctxPriv
                }
          }
  runEdhTx etsSandbox $
    act $ \ !result -> edhSwitchState ets $ exitEdhTx exit result
  where
    !ctxPriv = edh'context ets

-- | Uncaught exception in any thread (main or a descendant) will terminate the
-- whole Edh program, see:
--   https://github.com/e-wrks/edh/tree/master/Tour#program--threading-model
driveEdhProgram ::
  TMVar (Either SomeException EdhValue) -> EdhWorld -> EdhTx -> IO ()
driveEdhProgram !haltResult !world !prog = do
  -- check async exception mask state
  getMaskingState >>= \case
    Unmasked -> return ()
    _ ->
      throwIO $
        EdhError
          UsageError
          "You don't run an Edh program with async exceptions masked"
          (toDyn nil)
          "<edh>"

  -- prepare program environment
  !mainThId <- myThreadId
  let onSideThreadExc :: SomeException -> IO ()
      onSideThreadExc !exc = case fromException exc of
        Just ThreadTerminate -> pure () -- not to affect main thread
        _ -> throwTo mainThId exc
  -- prepare the Edh thread forker
  !forkQueue <- newTBQueueIO 10

  let !eps =
        EdhProgState
          { edh'prog'world = world,
            edh'prog'main = mainThId,
            edh'prog'result = haltResult,
            edh'fork'queue = forkQueue
          }
      keepForking :: Int -> IO ()
      keepForking !trapDone =
        atomically
          ( (Nothing <$ readTMVar haltResult)
              `orElse` (Just <$> readTBQueue forkQueue)
          )
          >>= \case
            -- Edh program halted, done
            Nothing -> return ()
            Just (!etsForker, !actForkee) -> do
              !etsForkee <- deriveForkeeState etsForker
              -- bootstrap on the forkee thread
              atomically $
                writeTBQueue (edh'task'queue etsForkee) $
                  EdhDoSTM etsForkee $ False <$ actForkee etsForkee
              !forkeeThId <- uninterruptibleMask_ $
                forkIOWithUnmask $ \ !unmask ->
                  catch
                    ( driveEdhThread
                        eps
                        (edh'defers etsForkee)
                        (edh'task'queue etsForkee)
                        unmask
                    )
                    onSideThreadExc
              readIORef trapReq >>= \ !trapNo ->
                if trapNo == trapDone
                  then keepForking trapNo
                  else do
                    atomically $
                      logger
                        100
                        ( Just $
                            T.pack $
                              "Trap#" <> show trapNo
                                <> " Program "
                                <> show mainThId
                                <> " forked Edh "
                                <> show forkeeThId
                        )
                        $ getEdhErrCtx 0 etsForker
                    keepForking trapNo
        where
          -- derive thread state for the forkee thread
          deriveForkeeState :: EdhThreadState -> IO EdhThreadState
          deriveForkeeState !etsForker = do
            !descQueue <- newTBQueueIO 20
            !perceivers <- newTVarIO []
            !defers <- newTVarIO []
            return
              EdhThreadState
                { edh'thread'prog = edh'thread'prog etsForker,
                  edh'in'tx = False,
                  edh'task'queue = descQueue,
                  edh'perceivers = perceivers,
                  edh'defers = defers,
                  -- forkee inherits call stack etc in the context from forker, so
                  -- effect resolution and far-reaching exception handlers can work.
                  edh'context =
                    fromCtx
                      { edh'ctx'genr'caller = Nothing,
                        edh'ctx'match = true,
                        edh'ctx'pure = False,
                        edh'ctx'exp'target = Nothing,
                        edh'ctx'eff'target = Nothing
                      }
                }
            where
              !fromCtx = edh'context etsForker
  -- start forker thread
  void $
    mask_ $
      forkIOWithUnmask $ \ !unmask ->
        catch (unmask $ keepForking =<< readIORef trapReq) onSideThreadExc
  -- start the main thread
  flip
    finally
    -- set halt result after the main thread done, anyway if not already,
    -- so all side threads will terminate
    (atomically $ void $ tryPutTMVar haltResult (Right nil))
    $ handle
      ( \(e :: SomeException) -> case fromException e :: Maybe EdhError of
          Just (ProgramHalt !phd) -> case fromDynamic phd :: Maybe EdhValue of
            Just !phv -> atomically $ void $ tryPutTMVar haltResult $ Right phv
            _ -> case fromDynamic phd :: Maybe SomeException of
              Just !phe ->
                atomically $ void $ tryPutTMVar haltResult (Left phe)
              Nothing -> atomically $ void $ tryPutTMVar haltResult (Left e)
          Just _ -> atomically $ void $ tryPutTMVar haltResult (Left e)
          Nothing -> do
            atomically $ void $ tryPutTMVar haltResult (Left e)
            throwIO e -- re-throw if the exception is unknown
      )
      $ do
        -- prepare program state for main Edh thread
        !mainQueue <- newTBQueueIO 30
        !perceivers <- newTVarIO []
        !defers <- newTVarIO []
        let !etsAtBoot =
              EdhThreadState
                { edh'thread'prog = eps,
                  edh'in'tx = False,
                  edh'task'queue = mainQueue,
                  edh'perceivers = perceivers,
                  edh'defers = defers,
                  edh'context = worldContext world
                }
        -- bootstrap the program on main Edh thread
        atomically $
          writeTBQueue mainQueue $
            EdhDoSTM etsAtBoot $ False <$ prog etsAtBoot
        -- drive the main Edh thread
        uninterruptibleMask $ driveEdhThread eps defers mainQueue
  where
    !trapReq = edh'trap'request world
    !console = edh'world'console world
    !logger = consoleLogger console

drivePerceiver ::
  EdhValue ->
  EdhThreadState ->
  (TVar Bool -> EdhTx) ->
  (forall a. IO a -> IO a) ->
  IO Bool
drivePerceiver !ev !etsOrigin !reaction !unmask = do
  !breakThread <- newTVarIO False
  !reactPerceivers <- newTVarIO []
  !reactDefers <- newTVarIO []
  !reactTaskQueue <- newTBQueueIO 10
  let !etsPerceiver =
        etsOrigin
          { edh'in'tx = False,
            edh'task'queue = reactTaskQueue,
            edh'perceivers = reactPerceivers,
            edh'defers = reactDefers,
            edh'context =
              (edh'context etsOrigin)
                { edh'ctx'genr'caller = Nothing,
                  edh'ctx'match = ev,
                  -- todo should set pure to True or False here?
                  --      or just inherit as is?
                  -- edh'ctx'pure = True,
                  edh'ctx'exp'target = Nothing,
                  edh'ctx'eff'target = Nothing
                }
          }
  atomically $
    writeTBQueue reactTaskQueue $
      EdhDoSTM etsPerceiver $ False <$ reaction breakThread etsPerceiver
  driveEdhThread (edh'thread'prog etsOrigin) reactDefers reactTaskQueue unmask
  readTVarIO breakThread

driveEdhThread ::
  EdhProgState ->
  TVar [DeferRecord] ->
  TBQueue EdhTask ->
  (forall a. IO a -> IO a) ->
  IO ()
driveEdhThread !eps !defers !tq !unmask = readIORef trapReq >>= taskLoop
  where
    !mainThId = edh'prog'main eps
    !world = edh'prog'world eps
    !trapReq = edh'trap'request world
    !console = edh'world'console world
    !logger = consoleLogger console

    !edhWrapException = edh'exception'wrapper $ edh'prog'world eps
    nextTaskFromQueue :: TBQueue EdhTask -> STM (Maybe EdhTask)
    nextTaskFromQueue =
      orElse (Nothing <$ readTMVar (edh'prog'result eps)) . tryReadTBQueue

    drivePerceivers :: [(EdhValue, PerceiveRecord)] -> IO Bool
    drivePerceivers [] = return False
    drivePerceivers ((!ev, PerceiveRecord _ !etsOrigin !reaction) : rest) =
      drivePerceiver ev etsOrigin reaction unmask >>= \case
        True -> return True
        False -> drivePerceivers rest

    driveDefers :: IO () -> [DeferRecord] -> IO ()
    driveDefers !done !records =
      newIORef done >>= \ !doneVar -> do
        let go :: [DeferRecord] -> IO ()
            go [] = join $ readIORef doneVar
            go ((DeferRecord !etsDefer !deferredProc) : restDefers) = do
              !deferPerceivers <- newTVarIO []
              !deferDefers <- newTVarIO []
              !deferTaskQueue <- newTBQueueIO 10
              atomically $
                writeTBQueue deferTaskQueue $
                  EdhDoSTM etsDefer $
                    False
                      <$ deferredProc
                        etsDefer
                          { edh'in'tx = False,
                            edh'task'queue = deferTaskQueue,
                            edh'perceivers = deferPerceivers,
                            edh'defers = deferDefers
                          }
              try (driveEdhThread eps deferDefers deferTaskQueue unmask)
                >>= \case
                  Left (err :: SomeException) -> do
                    -- schedule it to be re-thrown after all defers executed
                    -- todo this overwrites previous ones if multiple errors
                    -- occurred, is it okay?
                    writeIORef doneVar (throwIO err)
                    driveDefers done restDefers
                  Right {} -> driveDefers done restDefers
        go records

    terminateThread :: IO () -> IO ()
    terminateThread !done = do
      !doneVar <- newIORef done
      !tqTerm <- newTBQueueIO 50
      let driveOut :: IO ()
          driveOut =
            atomically (nextTaskFromQueue tqTerm) >>= \case
              -- termination done, run defers lastly
              Nothing -> do
                !toBeDone <- readIORef doneVar
                readTVarIO defers >>= driveDefers toBeDone

              -- note during actIO, perceivers won't fire
              Just (EdhDoIO !etsOrig !actIO) ->
                let !ets = etsOrig {edh'task'queue = tqTerm}
                 in try actIO >>= \case
                      -- terminate this thread, we are already doing it
                      Right True -> driveOut
                      -- continue running rest cleanup txs
                      Right False -> driveOut
                      Left (e :: SomeException) -> case edhKnownError e of
                        -- terminate this thread, we are already doing it
                        Just ThreadTerminate -> driveOut
                        -- uncaught error on cleanup, schedule it to be finally
                        -- propagated to main thread
                        -- todo this overwrites previous errors when multiple
                        -- occurred, is it okay?
                        Just !err -> do
                          writeIORef doneVar (throwIO err)
                          driveOut

                        -- give a chance for the Edh code to handle an unknown
                        -- exception
                        Nothing -> do
                          atomically $
                            edhWrapException (Just ets) e >>= \ !exo ->
                              writeTBQueue tqTerm $
                                EdhDoSTM ets $
                                  False <$ edhThrow ets (EdhObject exo)
                          -- continue running rest cleanup txs
                          driveOut
              Just (EdhDoSTM !etsOrig !actSTM) ->
                let !ets = etsOrig {edh'task'queue = tqTerm}
                 in try (goSTM ets actSTM) >>= \case
                      -- terminate this thread, we are already doing it
                      Right True -> driveOut
                      -- continue running rest cleanup txs
                      Right False -> driveOut
                      Left (e :: SomeException) -> case edhKnownError e of
                        -- terminate this thread, we are already doing it
                        Just ThreadTerminate -> driveOut
                        -- uncaught error on cleanup, schedule it to be finally
                        -- propagated to main thread
                        -- todo this overwrites previous errors when multiple
                        -- occurred, is it okay?
                        Just !err -> do
                          writeIORef doneVar (throwIO err)
                          driveOut

                        -- give a chance for the Edh code to handle an unknown
                        -- exception
                        Nothing -> do
                          atomically $
                            edhWrapException (Just ets) e >>= \ !exo ->
                              writeTBQueue tqTerm $
                                EdhDoSTM ets $
                                  False
                                    <$ edhThrow
                                      ets
                                      (EdhObject exo)
                          -- continue running rest cleanup txs
                          driveOut

      atomically (edhWrapException Nothing $ toException ThreadTerminate)
        >>= \ !termExObj ->
          let !termExVal = EdhObject termExObj
              throwIn :: IO ()
              throwIn =
                atomically (nextTaskFromQueue tq) >>= \case
                  -- all pending txs got a ThreadTerminate() thrown in,
                  -- drive their consequences out
                  Nothing -> driveOut
                  Just (EdhDoIO !etsOrig _actIO) ->
                    let !ets = etsOrig {edh'task'queue = tqTerm}
                     in do
                          atomically $
                            writeTBQueue tqTerm $
                              EdhDoSTM ets $ True <$ edhThrow ets termExVal
                          throwIn
                  Just (EdhDoSTM !etsOrig _actSTM) ->
                    let !ets = etsOrig {edh'task'queue = tqTerm}
                     in do
                          atomically $
                            writeTBQueue tqTerm $
                              EdhDoSTM ets $ True <$ edhThrow ets termExVal
                          throwIn
           in throwIn

    taskLoop !trapDone = do
      !trapNo <- readIORef trapReq
      !nextTask <- atomically (nextTaskFromQueue tq)
      !trapStartNS <-
        if trapNo == trapDone
          then return 0
          else getMonotonicTimeNSec
      oneTask trapNo trapStartNS nextTask
      where
        oneTask !trapDone' !trapStartNS = \case
          -- this thread is done, go terminate it
          Nothing -> terminateThread (return ())
          -- note during actIO, perceivers won't fire, program termination
          -- won't stop this thread
          Just (EdhDoIO !etsOrig !actIO) -> do
            let !ets = etsOrig {edh'task'queue = tq}
            try (unmask actIO) >>= doneOne ets
          Just (EdhDoSTM !etsOrig !actSTM) -> do
            let !ets = etsOrig {edh'task'queue = tq}
            try (unmask $ goSTM ets actSTM) >>= doneOne ets
          where
            doneOne !etsDone !result = do
              unless (trapStartNS == 0) $ do
                !doneNS <- getMonotonicTimeNSec
                let !secCost =
                      -- leverage lossless decimal's pretty show of numbers
                      (fromIntegral (doneNS - trapStartNS) :: Decimal) / 1e9
                !thId <- myThreadId
                atomically $
                  logger
                    100
                    ( Just $
                        T.pack $
                          "Trap#" <> show trapDone'
                            <> " Program "
                            <> show mainThId
                            <> " Edh "
                            <> show thId
                            <> " tx cost "
                            <> show secCost
                            <> " second(s)"
                    )
                    $ getEdhErrCtx 0 etsDone

              !trapNo <- readIORef trapReq
              unless (trapNo == trapDone') $ do
                !thId <- myThreadId
                atomically $
                  logger
                    100
                    ( Just $
                        T.pack $
                          "Trap#" <> show trapNo
                            <> " Program "
                            <> show mainThId
                            <> " Edh "
                            <> show thId
                            <> " tx done"
                    )
                    $ getEdhErrCtx 0 etsDone

              case result of
                -- terminate this thread
                Right True -> terminateThread (return ())
                -- continue running this thread
                Right False -> do
                  !nextTask <- atomically (nextTaskFromQueue tq)
                  !trapStartNS' <-
                    if trapNo == trapDone'
                      then return 0
                      else getMonotonicTimeNSec
                  oneTask trapNo trapStartNS' nextTask
                Left (e :: SomeException) -> case edhKnownError e of
                  -- explicit terminate requested
                  Just ThreadTerminate -> terminateThread (return ())
                  -- this'll propagate to main thread if not on it
                  Just !err -> terminateThread (throwIO err)
                  -- give a chance for the Edh code to handle an unknown
                  -- exception
                  Nothing -> do
                    atomically $
                      edhWrapException (Just etsDone) e
                        >>= \ !exo ->
                          writeTBQueue tq $
                            EdhDoSTM etsDone $
                              False <$ edhThrow etsDone (EdhObject exo)
                    -- continue running this thread for the queued exception
                    -- handler
                    !nextTask <- atomically (nextTaskFromQueue tq)
                    !trapStartNS' <-
                      if trapNo == trapDone'
                        then return 0
                        else getMonotonicTimeNSec
                    oneTask trapNo trapStartNS' nextTask

    goSTM :: EdhThreadState -> STM Bool -> IO Bool
    goSTM !etsTask !actTask = loopSTM
      where
        loopSTM :: IO Bool
        loopSTM =
          atomically stmJob >>= \case
            Nothing -> return True -- program halted, terminate this thread
            Just (Right !toTerm) ->
              -- no perceiver has fired, the tx job has already been executed
              return toTerm
            Just (Left !gotevl) ->
              drivePerceivers gotevl >>= \case
                True -> do
                  -- a perceiver is terminating this thread, the task action
                  -- has not been executed, re-queue it so it can get notified
                  -- by a ThreadTerminate exception.
                  -- the etsTask will provide the target context to where a
                  -- ThreadTerminate exception will be thrown at
                  atomically $ writeTBQueue tq $ EdhDoSTM etsTask (return True)
                  return True
                False ->
                  -- there've been one or more perceivers fired, the tx job have
                  -- been skipped, as no perceiver is terminating the thread,
                  -- continue with this tx job
                  loopSTM

        -- this is the STM work package, where perceivers can preempt the
        -- inline job on an Edh thread
        stmJob :: STM (Maybe (Either [(EdhValue, PerceiveRecord)] Bool))
        stmJob =
          tryReadTMVar (edh'prog'result eps) >>= \case
            Just _ -> return Nothing -- program halted
            Nothing ->
              -- program still running
              (readTVar (edh'perceivers etsTask) >>= perceiverChk [])
                >>= \ !gotevl ->
                  if null gotevl
                    then -- no perceiver fires, execute the tx job
                      Just . Right <$> actTask
                    else -- skip the tx job if at least one perceiver fires
                      return $ Just $ Left gotevl

        perceiverChk ::
          [(EdhValue, PerceiveRecord)] ->
          [PerceiveRecord] ->
          STM [(EdhValue, PerceiveRecord)]
        perceiverChk !gotevl [] = return gotevl
        perceiverChk !gotevl (r@(PerceiveRecord !evc _ _) : rest) =
          tryReadTChan evc >>= \case
            Just !ev -> perceiverChk ((ev, r) : gotevl) rest
            Nothing -> perceiverChk gotevl rest

-- | make an effectful call from current Edh context
--
-- if performing from an effectful procedure call, use the outer stack of
-- that call in effect resolution
--
-- otherwise this is the same as 'behaveEdhEffect'
performEdhEffect ::
  AttrKey ->
  [EdhValue] ->
  [(AttrName, EdhValue)] ->
  (EdhValue -> EdhTx) ->
  EdhTx
performEdhEffect !effKey !args !kwargs !exit !ets =
  resolveEdhPerform ets effKey $ \ !effVal ->
    runEdhTx ets $
      edhMakeCall'
        effVal
        (ArgsPack args $ odFromList $ [(AttrByName k, v) | (k, v) <- kwargs])
        exit

-- | obtain an effectful value from current Edh context
--
-- if performing from an effectful procedure call, use the outer stack of
-- that call in effect resolution
--
-- otherwise this is the same as 'behaveEdhEffect''
performEdhEffect' :: AttrKey -> (Maybe EdhValue -> EdhTx) -> EdhTx
performEdhEffect' !effKey !exit !ets =
  resolveEdhPerform' ets effKey $ runEdhTx ets . exit

-- | make an effectful call from current Edh context
--
-- use full stack in effect resolution, may create infinite loops in effectful
-- procedure calls if one effectful procedure would make unconditional
-- recursive effectful call into itself, or there is some mutually recursive
-- pattern between multiple procedures
behaveEdhEffect ::
  AttrKey ->
  [EdhValue] ->
  [(AttrName, EdhValue)] ->
  (EdhValue -> EdhTx) ->
  EdhTx
behaveEdhEffect !effKey !args !kwargs !exit !ets =
  resolveEdhBehave ets effKey $ \ !effVal ->
    runEdhTx ets $
      edhMakeCall'
        effVal
        (ArgsPack args $ odFromList $ [(AttrByName k, v) | (k, v) <- kwargs])
        exit

-- | obtain an effectful value from current Edh context
--
-- use full stack in effect resolution
behaveEdhEffect' :: AttrKey -> (Maybe EdhValue -> EdhTx) -> EdhTx
behaveEdhEffect' !effKey !exit !ets =
  resolveEdhBehave' ets effKey $ runEdhTx ets . exit

-- | make a default effectful call from current Edh context
--
-- lookup effectful defaults instead of effects
--
-- use full stack in effect resolution, may create infinite loops in effectful
-- procedure calls if one effectful procedure would make unconditional
-- recursive effectful call into itself, or there is some mutually recursive
-- pattern between multiple procedures
fallbackEdhEffect ::
  AttrKey ->
  [EdhValue] ->
  [(AttrName, EdhValue)] ->
  (EdhValue -> EdhTx) ->
  EdhTx
fallbackEdhEffect !effKey !args !kwargs !exit !ets =
  resolveEdhFallback ets effKey $ \ !effVal ->
    runEdhTx ets $
      edhMakeCall'
        effVal
        (ArgsPack args $ odFromList $ [(AttrByName k, v) | (k, v) <- kwargs])
        exit

-- | obtain an effectful value from current Edh context
--
-- lookup effectful defaults instead of effects
--
-- use full stack in effect resolution
fallbackEdhEffect' :: AttrKey -> (Maybe EdhValue -> EdhTx) -> EdhTx
fallbackEdhEffect' !effKey !exit !ets =
  resolveEdhFallback' ets effKey $ runEdhTx ets . exit
