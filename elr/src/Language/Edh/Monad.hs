module Language.Edh.Monad where

-- import Debug.Trace
-- import GHC.Stack

import Control.Applicative
import Control.Concurrent.STM
import Control.Exception
import Control.Monad.State.Strict
import qualified Data.ByteString as B
import Data.Dynamic
import Data.IORef
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Data.Unique
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Control
import Language.Edh.CoreLang
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.RtTypes
import Prelude

-- * Monadic Edh Interface

newtype Edh a = Edh
  { unEdh :: ([(ErrMessage, ErrContext)] -> STM ()) -> EdhTxExit a -> EdhTx
  }

-- | Wrap a CPS procedure as 'Edh' computation
--
-- CAVEAT: This is call/CC equivalent, be alerted that you've stepped out of
-- the "Structured Programming" zone by using it.
mEdh :: forall a. (EdhTxExit a -> EdhTx) -> Edh a
mEdh act = Edh $ \_naExit exit -> act exit

-- | Wrap a CPS procedure as 'Edh' computation
--
-- CAVEAT: This is call/CC equivalent, be alerted that you've stepped out of
-- the "Structured Programming" zone by using it.
mEdh' :: forall a. (EdhTxExit ErrMessage -> EdhTxExit a -> EdhTx) -> Edh a
mEdh' act = Edh $ \naExit exit -> do
  let naExit' :: EdhTxExit ErrMessage
      naExit' !msg !ets = naExit [(msg, getEdhErrCtx 0 ets)]
  act naExit' exit

naM :: forall a. ErrMessage -> Edh a
naM msg = mEdh' $ \naExit _exit -> naExit msg

runEdh :: EdhThreadState -> Edh a -> EdhTxExit a -> STM ()
runEdh ets ma exit = runEdhTx ets $ unEdh ma rptEdhNotApplicable exit

rptEdhNotApplicable :: [(ErrMessage, ErrContext)] -> STM ()
rptEdhNotApplicable errs =
  throwSTM $
    EdhError EvalError "❌  No Edh action applicable" (toDyn nil) $
      T.unlines $
        ( \(msg, ctx) ->
            if T.null ctx
              then "⛔ " <> msg
              else ctx <> "\n⛔ " <> msg
        )
          <$> errs

instance Functor Edh where
  fmap f edh = Edh $ \naExit exit -> unEdh edh naExit $ \a -> exit $ f a
  {-# INLINE fmap #-}

instance Applicative Edh where
  pure a = Edh $ \_naExit exit -> exit a
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad Edh where
  return = pure
  {-# INLINE return #-}
  m >>= k = Edh $ \naExit c -> unEdh m naExit (\x -> unEdh (k x) naExit c)
  {-# INLINE (>>=) #-}

instance Alternative Edh where
  empty = Edh $ \naExit _exit _ets -> naExit []
  x <|> y = Edh $ \naExit exit ets ->
    unEdh x (\errOut -> unEdh y (naExit . (++ errOut)) exit ets) exit ets

instance MonadPlus Edh

inlineSTM :: STM a -> Edh a
inlineSTM act = Edh $ \_naExit exit ets -> act >>= (`exit` ets)
{-# INLINE inlineSTM #-}

liftSTM :: STM a -> Edh a
liftSTM act = Edh $ \_naExit exit ets ->
  runEdhTx ets $
    edhContSTM $
      act >>= exitEdh ets exit
{-# INLINE liftSTM #-}

liftEdhTx :: EdhTx -> Edh ()
liftEdhTx tx = Edh $ \_naExit exit ets -> tx ets >> exit () ets

instance MonadIO Edh where
  liftIO act = Edh $ \_naExit exit ets ->
    runEdhTx ets $
      edhContIO $
        act >>= atomically . exitEdh ets exit
  {-# INLINE liftIO #-}

-- ** Attribute Resolution

resolveEdhAttrAddrM :: AttrAddr -> Edh AttrKey
resolveEdhAttrAddrM (NamedAttr !attrName) = return (AttrByName attrName)
resolveEdhAttrAddrM (QuaintAttr !attrName) = return (AttrByName attrName)
resolveEdhAttrAddrM (SymbolicAttr !symName) = do
  !ets <- edhThreadState
  let scope = contextScope $ edh'context ets
  inlineSTM (resolveEdhCtxAttr scope $ AttrByName symName) >>= \case
    Just (!val, _) -> case val of
      (EdhSymbol !symVal) -> return (AttrBySym symVal)
      (EdhString !nameVal) -> return (AttrByName nameVal)
      _ ->
        throwEdhM EvalError $
          "not a symbol/string as "
            <> symName
            <> ", it is a "
            <> edhTypeNameOf val
            <> ": "
            <> T.pack (show val)
    Nothing ->
      throwEdhM EvalError $
        "no symbol/string named "
          <> T.pack (show symName)
          <> " available"
resolveEdhAttrAddrM (IntplSymAttr src !x) = mEdh $ \exit ->
  evalExprSrc x $ \ !symVal -> case edhUltimate symVal of
    EdhSymbol !sym -> exitEdhTx exit $ AttrBySym sym
    EdhString !nm -> exitEdhTx exit $ AttrByName nm
    _ -> edhSimpleDescTx symVal $ \ !badDesc ->
      throwEdhTx UsageError $
        "symbol interpolation given unexpected value: "
          <> badDesc
          <> "\n 🔣  evaluated from @( "
          <> src
          <> " )"
resolveEdhAttrAddrM (LitSymAttr !sym) = return $ AttrBySym sym
resolveEdhAttrAddrM MissedAttrName =
  throwEdhM
    EvalError
    "incomplete syntax: missing attribute name"
resolveEdhAttrAddrM MissedAttrSymbol =
  throwEdhM
    EvalError
    "incomplete syntax: missing symbolic attribute name"
{-# INLINE resolveEdhAttrAddrM #-}

edhValueAsAttrKeyM :: EdhValue -> Edh AttrKey
edhValueAsAttrKeyM !keyVal = case edhUltimate keyVal of
  EdhString !attrName -> return $ AttrByName attrName
  EdhSymbol !sym -> return $ AttrBySym sym
  EdhExpr _ _ (AttrExpr (DirectRef (AttrAddrSrc !addr _))) _ ->
    resolveEdhAttrAddrM addr
  _ -> do
    !badDesc <- edhSimpleDescM keyVal
    throwEdhM EvalError $ "not a valid attribute key: " <> badDesc

-- ** Effect Resolution

performM :: AttrKey -> Edh EdhValue
performM !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhPerform ets effKey $ exitEdh ets exit

performM' :: AttrKey -> Edh (Maybe EdhValue)
performM' !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhPerform' ets effKey $ exitEdh ets exit

behaveM :: AttrKey -> Edh EdhValue
behaveM !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhBehave ets effKey $ exitEdh ets exit

behaveM' :: AttrKey -> Edh (Maybe EdhValue)
behaveM' !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhBehave' ets effKey $ exitEdh ets exit

fallbackM :: AttrKey -> Edh EdhValue
fallbackM !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhFallback ets effKey $ exitEdh ets exit

fallbackM' :: AttrKey -> Edh (Maybe EdhValue)
fallbackM' !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhFallback' ets effKey $ exitEdh ets exit

-- ** Utilities

edhThreadState :: Edh EdhThreadState
edhThreadState = Edh $ \_naExit exit ets -> exit ets ets
{-# INLINE edhThreadState #-}

edhProgramState :: Edh EdhProgState
edhProgramState = Edh $ \_naExit exit ets -> exit (edh'thread'prog ets) ets
{-# INLINE edhProgramState #-}

newTVarEdh :: forall a. a -> Edh (TVar a)
newTVarEdh = inlineSTM . newTVar
{-# INLINE newTVarEdh #-}

readTVarEdh :: forall a. TVar a -> Edh a
readTVarEdh = inlineSTM . readTVar
{-# INLINE readTVarEdh #-}

writeTVarEdh :: forall a. TVar a -> a -> Edh ()
writeTVarEdh ref v = inlineSTM $ writeTVar ref v
{-# INLINE writeTVarEdh #-}

newIORefEdh :: forall a. a -> Edh (IORef a)
newIORefEdh = liftIO . newIORef
{-# INLINE newIORefEdh #-}

readIORefEdh :: forall a. IORef a -> Edh a
readIORefEdh = liftIO . readIORef
{-# INLINE readIORefEdh #-}

writeIORefEdh :: forall a. IORef a -> a -> Edh ()
writeIORefEdh ref v = liftIO $ writeIORef ref v
{-# INLINE writeIORefEdh #-}

newUniqueEdh :: Edh Unique
-- todo: safer impl. ?
-- note: liftIO/edhContIO here will break `ai` transactions if specified by
--       scripting code, there sure be scenarios in need of new Unique id(s)
--       but too bad to sacrifice `ai`-ability
newUniqueEdh = inlineSTM $ unsafeIOToSTM newUnique
{-# INLINE newUniqueEdh #-}

-- ** Call Making & Context Manipulation

callM :: EdhValue -> [ArgSender] -> Edh EdhValue
callM callee apkr = Edh $ \_naExit -> edhMakeCall callee apkr

callM' :: EdhValue -> ArgsPack -> Edh EdhValue
callM' callee apk = Edh $ \_naExit -> edhMakeCall' callee apk

callMagicM :: Object -> AttrKey -> ArgsPack -> Edh EdhValue
callMagicM obj magicKey apk =
  Edh $ \_naExit -> callMagicMethod obj magicKey apk

pushStackM :: Edh a -> Edh a
pushStackM !act = do
  !ets <- edhThreadState
  let !scope = edh'frame'scope $ edh'ctx'tip $ edh'context ets
  !scope' <- inlineSTM $ newNestedScope scope
  pushStackM' scope' act

pushStackM' :: Scope -> Edh a -> Edh a
pushStackM' !scope !act = Edh $ \naExit exit ets -> do
  let !ctx = edh'context ets
      !tip = edh'ctx'tip ctx

      !etsNew = ets {edh'context = ctxNew}
      !ctxNew =
        ctx
          { edh'ctx'tip = tipNew,
            edh'ctx'stack = tip : edh'ctx'stack ctx
          }
      !tipNew =
        tip
          { edh'frame'scope = scope,
            edh'exc'handler = defaultEdhExcptHndlr
          }
  unEdh act naExit (edhSwitchState ets . exit) etsNew

-- ** Value Manipulations

edhObjStrM :: Object -> Edh Text
edhObjStrM !o = Edh $ \_naExit !exit !ets ->
  edhObjStr ets o $ exitEdh ets exit

edhValueStrM :: EdhValue -> Edh Text
edhValueStrM !v = Edh $ \_naExit !exit !ets ->
  edhValueStr ets v $ exitEdh ets exit

edhObjReprM :: Object -> Edh Text
edhObjReprM !o = Edh $ \_naExit !exit !ets ->
  edhObjRepr ets o $ exitEdh ets exit

edhValueReprM :: EdhValue -> Edh Text
edhValueReprM !v = Edh $ \_naExit !exit !ets ->
  edhValueRepr ets v $ exitEdh ets exit

edhObjDescM :: Object -> Edh Text
edhObjDescM !o = Edh $ \_naExit !exit !ets ->
  edhObjDesc ets o $ exitEdh ets exit

edhValueDescM :: EdhValue -> Edh Text
edhValueDescM !v = Edh $ \_naExit !exit !ets ->
  edhValueDesc ets v $ exitEdh ets exit

edhSimpleDescM :: EdhValue -> Edh Text
edhSimpleDescM !v = Edh $ \_naExit !exit !ets ->
  edhSimpleDesc ets v $ exitEdh ets exit

edhValueNullM :: EdhValue -> Edh Bool
edhValueNullM !v = Edh $ \_naExit !exit !ets ->
  edhValueNull ets v $ exitEdh ets exit

edhValueJsonM :: EdhValue -> Edh Text
edhValueJsonM !v = Edh $ \_naExit !exit !ets ->
  edhValueJson ets v $ exitEdh ets exit

edhValueBlobM :: EdhValue -> Edh B.ByteString
edhValueBlobM !v = Edh $ \_naExit !exit !ets ->
  edhValueBlob ets v $ exitEdh ets exit

edhValueBlobM' :: EdhValue -> Edh (Maybe B.ByteString)
edhValueBlobM' !v = Edh $ \_naExit !exit !ets ->
  edhValueBlob' ets v (exitEdh ets exit Nothing) $ exitEdh ets exit . Just

parseEdhIndexM :: EdhValue -> Edh (Either Text EdhIndex)
parseEdhIndexM !val = Edh $ \_naExit !exit !ets ->
  parseEdhIndex ets val $ exitEdh ets exit

regulateEdhIndexM :: Int -> Int -> Edh Int
regulateEdhIndexM !len !idx =
  if posIdx < 0 || posIdx >= len
    then
      throwEdhM EvalError $
        "index out of bounds: "
          <> T.pack (show idx)
          <> " vs "
          <> T.pack (show len)
    else return posIdx
  where
    !posIdx =
      if idx < 0 -- Python style negative index
        then idx + len
        else idx

regulateEdhSliceM ::
  Int -> (Maybe Int, Maybe Int, Maybe Int) -> Edh (Int, Int, Int)
regulateEdhSliceM !len !slice = Edh $ \_naExit !exit !ets ->
  regulateEdhSlice ets len slice $ exitEdh ets exit

-- ** Exception Throwing & Handling

throwEdhM :: EdhErrorTag -> Text -> Edh a
throwEdhM tag msg = throwEdhM' tag msg []
{-# INLINE throwEdhM #-}

throwEdhM' :: EdhErrorTag -> Text -> [(AttrKey, EdhValue)] -> Edh a
throwEdhM' tag msg details = Edh $ \_naExit _exit ets -> do
  let !edhErr = EdhError tag msg errDetails $ getEdhErrCtx 0 ets
      !edhWrapException =
        edh'exception'wrapper (edh'prog'world $ edh'thread'prog ets)
      !errDetails = case details of
        [] -> toDyn nil
        _ -> toDyn $ EdhArgsPack $ ArgsPack [] $ odFromList details
  edhWrapException (Just ets) (toException edhErr)
    >>= \ !exo -> edhThrow ets $ EdhObject exo
{-# INLINE throwEdhM' #-}

-- ** Artifacts Making

wrapM :: Typeable t => t -> Edh Object
wrapM t = do
  !ets <- edhThreadState
  let world = edh'prog'world $ edh'thread'prog ets
      edhWrapValue = edh'value'wrapper world Nothing
  inlineSTM $ edhWrapValue $ toDyn t

wrapM' :: Typeable t => Text -> t -> Edh Object
wrapM' !repr t = do
  !ets <- edhThreadState
  let world = edh'prog'world $ edh'thread'prog ets
      edhWrapValue = edh'value'wrapper world (Just repr)
  inlineSTM $ edhWrapValue $ toDyn t

wrapM'' :: Text -> Dynamic -> Edh Object
wrapM'' !repr !dd = do
  !ets <- edhThreadState
  let world = edh'prog'world $ edh'thread'prog ets
      edhWrapValue = edh'value'wrapper world (Just repr)
  inlineSTM $ edhWrapValue dd

mkEdhProc ::
  (ProcDefi -> EdhProcDefi) ->
  AttrName ->
  (ArgsPack -> Edh EdhValue, ArgsReceiver) ->
  Edh EdhValue
mkEdhProc !vc !nm (!p, _args) = do
  !ets <- edhThreadState
  !u <- newUniqueEdh
  return $
    EdhProcedure
      ( vc
          ProcDefi
            { edh'procedure'ident = u,
              edh'procedure'name = AttrByName nm,
              edh'procedure'lexi = contextScope $ edh'context ets,
              edh'procedure'doc = NoDocCmt,
              edh'procedure'decl = HostDecl $
                \apk -> unEdh (p apk) rptEdhNotApplicable
            }
      )
      Nothing

mkEdhClass ::
  AttrName ->
  (ArgsPack -> Edh (Maybe Unique, ObjectStore)) ->
  [Object] ->
  Edh () ->
  Edh Object
mkEdhClass !clsName !allocator !superClasses !clsBody = do
  !ets <- edhThreadState
  !classStore <- inlineSTM iopdEmpty
  !idCls <- newUniqueEdh
  !ssCls <- newTVarEdh superClasses
  !mroCls <- newTVarEdh []
  let !scope = contextScope $ edh'context ets
      !metaClassObj =
        edh'obj'class $ edh'obj'class $ edh'scope'this $ rootScopeOf scope
      !clsProc =
        ProcDefi
          idCls
          (AttrByName clsName)
          scope
          NoDocCmt
          (HostDecl fakeHostProc)
      !cls = Class clsProc classStore allocator' mroCls
      !clsObj = Object idCls (ClassStore cls) metaClassObj ssCls
      !clsScope =
        scope
          { edh'scope'entity = classStore,
            edh'scope'this = clsObj,
            edh'scope'that = clsObj,
            edh'scope'proc = clsProc,
            edh'effects'stack = []
          }
  pushStackM' clsScope clsBody
  !mroInvalid <- inlineSTM $ fillClassMRO cls superClasses
  unless (T.null mroInvalid) $ throwEdhM UsageError mroInvalid
  return clsObj
  where
    fakeHostProc :: ArgsPack -> EdhHostProc
    fakeHostProc _ !exit = exitEdhTx exit nil

    allocator' :: ArgsPack -> EdhObjectAllocator
    allocator' apk ctorExit ets =
      unEdh
        (allocator apk)
        rptEdhNotApplicable
        (\(maybeIdent, oStore) _ets -> ctorExit maybeIdent oStore)
        ets
