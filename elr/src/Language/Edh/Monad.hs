module Language.Edh.Monad where

-- import Debug.Trace
-- import GHC.Stack

import Control.Applicative
import Control.Concurrent.STM
import Control.Exception
import Control.Monad.State.Strict
import qualified Data.ByteString as B
import Data.Dynamic
import Data.Hashable
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

-- TODO implement exception catching, then async exception masking,
--      then 'bracket'; for 'EIO' at least, possibly for 'Edh' too.

-- | Scriptability enabling monad
--
-- The @Edh@ monad is friendly to scripted concurrency and transactional
-- semantics, i.e. event perceivers, the @ai@ keyword for transaction grouping.
--
-- Note @Edh@ is rather slow in run speed, as a cost of scriptability.
--
-- CAVEAT: An @ai@ block as by the scripting code will be broken, thus an
--         exception thrown, wherever any 'liftSTM' 'liftEIO' or 'liftIO' is
--         issued in execution of that block.
newtype Edh a = Edh
  { -- | This should seldom be used directly
    unEdh :: ([(ErrMessage, ErrContext)] -> STM ()) -> EdhTxExit a -> EdhTx
  }

-- | Wrap a CPS procedure as 'Edh' computation
--
-- CAVEAT: This is call/CC equivalent, be alert that you've stepped out of
-- the "Structured Programming" zone by using this.
mEdh :: forall a. (EdhTxExit a -> EdhTx) -> Edh a
mEdh act = Edh $ \_naExit exit -> act exit

-- | Wrap a CPS procedure as 'Edh' computation
--
-- CAVEAT: This is call/CC equivalent, be alert that you've stepped out of
-- the "Structured Programming" zone by using this.
mEdh' :: forall a. (EdhTxExit ErrMessage -> EdhTxExit a -> EdhTx) -> Edh a
mEdh' act = Edh $ \naExit exit -> do
  let naExit' :: EdhTxExit ErrMessage
      naExit' !msg !ets = naExit [(msg, getEdhErrCtx 0 ets)]
  act naExit' exit

-- | Signal __Not/Applicable__ with an error message
--
-- This will cause an 'Alternative' action to be tried, per
-- 'MonadPlus' semantics. An exception will be thrown with accumulated @naM@
-- error messages, if none of the alternative actions can settle with a result.
naM :: forall a. ErrMessage -> Edh a
naM msg = mEdh' $ \naExit _exit -> naExit msg

-- | Run an 'Edh' action from within an @'STM' ()@ action
--
-- CAVEAT:
--
-- * You would better make sure the calling Haskell thread owns the
--   'EdhThreadState', or the 1st transaction will be carried out in
--   current thread, and following transactions will be carried out in
--   the 'EdhThreadState''s owner thread, which is ridiculous. Even worse
--   when that @Edh@ thread has already been terminated, all subsequent
--   'STM' transactions will cease to happen, and your continuation never
--   executed too.
-- * Don't follow such a call with subsequent 'STM' actions, that's usually
--   wrong. Unless interleaved "scripting threads" sharing the Haskell
--   thread are really intended.
--
-- Note: This call finishes as soon with the 1st 'STM' transaction within
--       the specified 'Edh' action, the continuation can be resumed rather
--       later after many subsequent 'STM' transactions performed, so
--       'catchSTM' or similar exception handling around such calls is usually
--        wrong.
runEdh :: EdhThreadState -> Edh a -> EdhTxExit a -> STM ()
runEdh ets ma exit = runEdhTx ets $ unEdh ma rptEdhNotApplicable exit

-- | Internal utility, you usually don't use this
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

-- | Perform the specified 'STM' action within current 'Edh' transaction
inlineSTM :: STM a -> Edh a
inlineSTM act = Edh $ \_naExit exit ets -> act >>= (`exit` ets)
{-# INLINE inlineSTM #-}

-- | Finish current 'Edh' transaction, perform the specified 'STM' action
-- in a new 'atomically' transaction, bind the result to the next 'Edh' action
--
-- CAVEAT: An @ai@ block as by the scripting code will be broken, thus an
--         exception thrown, wherever any 'liftSTM' 'liftEIO' or 'liftIO' is
--         issued in execution of that block.
liftSTM :: STM a -> Edh a
liftSTM act = Edh $ \_naExit exit ets ->
  runEdhTx ets $
    edhContSTM $
      act >>= exitEdh ets exit
{-# INLINE liftSTM #-}

-- | Lift an 'EdhTx' action as an 'Edh' action
liftEdhTx :: EdhTx -> Edh ()
liftEdhTx tx = Edh $ \_naExit exit ets -> tx ets >> exit () ets

instance MonadIO Edh where
  liftIO act = Edh $ \_naExit exit ets ->
    runEdhTx ets $
      edhContIO $
        act >>= atomically . exitEdh ets exit
  {-# INLINE liftIO #-}

-- ** Attribute Resolution

-- | Get a property from an @Edh@ object, with magics honored
getObjPropertyM :: Object -> AttrKey -> Edh EdhValue
getObjPropertyM !obj !key = mEdh' $ \naExit !exit -> do
  let exitNoAttr = edhObjDescTx obj $ \ !objDesc ->
        naExit $
          "no such property `" <> attrKeyStr key <> "` on object - " <> objDesc
  getObjProperty' obj key exitNoAttr exit

-- | Resolve an attribute addressor into an attribute key
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

-- | Coerce an @Edh@ value into an attribute key
--
-- Note only strings, symbols, and direct addressing expressions are valid,
-- other type of values will cause an exception thrown.
edhValueAsAttrKeyM :: EdhValue -> Edh AttrKey
edhValueAsAttrKeyM !keyVal = case edhUltimate keyVal of
  EdhString !attrName -> return $ AttrByName attrName
  EdhSymbol !sym -> return $ AttrBySym sym
  EdhExpr _ _ (AttrExpr (DirectRef (AttrAddrSrc !addr _))) _ ->
    resolveEdhAttrAddrM addr
  _ -> do
    !badDesc <- edhSimpleDescM keyVal
    throwEdhM EvalError $ "not a valid attribute key: " <> badDesc

-- | Prepare the exporting store for an object, you can put artifacts into it
-- so as to get them /exported/ from that specified object
prepareExpStoreM :: Object -> Edh EntityStore
prepareExpStoreM !fromObj = case edh'obj'store fromObj of
  HashStore !tgtEnt -> fromStore tgtEnt
  ClassStore !cls -> fromStore $ edh'class'store cls
  HostStore _ ->
    naM $
      "no way exporting with a host object of class " <> objClassName fromObj
  where
    fromStore tgtEnt = mEdh $ \exit ets ->
      (exitEdh ets exit =<<) $
        prepareMagicStore (AttrByName edhExportsMagicName) tgtEnt $
          edhCreateNsObj ets NoDocCmt phantomHostProc $ AttrByName "export"

-- | Import an @Edh@ module identified by the import spec
--
-- The spec can be absolute or relative to current context module.
importModuleM :: Text -> Edh Object
importModuleM !importSpec = mEdh $ \ !exit ->
  importEdhModule importSpec $ exitEdhTx exit

-- ** Effect Resolution

-- | Resolve an effectful artifact with @perform@ semantics
--
-- An exception is thrown if no such effect available
performM :: AttrKey -> Edh EdhValue
performM !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhPerform ets effKey $ exitEdh ets exit

-- | Resolve an effectful artifact with @perform@ semantics
--
-- 'Nothing' is returned if no such effect available
performM' :: AttrKey -> Edh (Maybe EdhValue)
performM' !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhPerform' ets effKey $ exitEdh ets exit

-- | Resolve an effectful artifact with @behave@ semantics
--
-- An exception is thrown when no such effect available
behaveM :: AttrKey -> Edh EdhValue
behaveM !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhBehave ets effKey $ exitEdh ets exit

-- | Resolve an effectful artifact with @behave@ semantics
--
-- 'Nothing' is returned if no such effect available
behaveM' :: AttrKey -> Edh (Maybe EdhValue)
behaveM' !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhBehave' ets effKey $ exitEdh ets exit

-- | Resolve an effectful artifact with @fallback@ semantics
--
-- An exception is thrown when no such effect available
fallbackM :: AttrKey -> Edh EdhValue
fallbackM !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhFallback ets effKey $ exitEdh ets exit

-- | Resolve an effectful artifact with @fallback@ semantics
--
-- 'Nothing' is returned if no such effect available
fallbackM' :: AttrKey -> Edh (Maybe EdhValue)
fallbackM' !effKey = Edh $ \_naExit !exit !ets ->
  resolveEdhFallback' ets effKey $ exitEdh ets exit

-- | Prepare the effecting store for the context scope, you can put artifacts
-- into it so as to make them /effective/ in current scope
prepareEffStoreM :: Edh EntityStore
prepareEffStoreM = prepareEffStoreM' $ AttrByName edhEffectsMagicName

-- | Prepare the specifically named effecting store for the context scope, you
-- can put artifacts into it so as to make them /effective/ in current scope
--
-- Note the naming is not stable yet, consider this an implementation details
-- for now.
prepareEffStoreM' :: AttrKey -> Edh EntityStore
prepareEffStoreM' !magicKey = mEdh $ \ !exit !ets ->
  exitEdh ets exit
    =<< prepareEffStore'
      magicKey
      ets
      (edh'scope'entity $ contextScope $ edh'context ets)

-- ** Edh Monad Utilities

-- | Extract the 'EdhThreadState' from current @Edh@ thread
edhThreadState :: Edh EdhThreadState
edhThreadState = Edh $ \_naExit exit ets -> exit ets ets
{-# INLINE edhThreadState #-}

-- | Extract the 'EdhProgState' from current @Edh@ thread
edhProgramState :: Edh EdhProgState
edhProgramState = Edh $ \_naExit exit ets -> exit (edh'thread'prog ets) ets
{-# INLINE edhProgramState #-}

-- | The 'STM' action lifted into 'Edh' monad
newTVarEdh :: forall a. a -> Edh (TVar a)
newTVarEdh = inlineSTM . newTVar
{-# INLINE newTVarEdh #-}

-- | The 'STM' action lifted into 'Edh' monad
readTVarEdh :: forall a. TVar a -> Edh a
readTVarEdh = inlineSTM . readTVar
{-# INLINE readTVarEdh #-}

-- | The 'STM' action lifted into 'Edh' monad
writeTVarEdh :: forall a. TVar a -> a -> Edh ()
writeTVarEdh ref v = inlineSTM $ writeTVar ref v
{-# INLINE writeTVarEdh #-}

-- | The 'STM' action lifted into 'Edh' monad
modifyTVarEdh' :: forall a. TVar a -> (a -> a) -> Edh ()
modifyTVarEdh' ref f = inlineSTM $ modifyTVar' ref f
{-# INLINE modifyTVarEdh' #-}

-- | The 'STM' action lifted into 'Edh' monad
newTMVarEdh :: forall a. a -> Edh (TMVar a)
newTMVarEdh = inlineSTM . newTMVar
{-# INLINE newTMVarEdh #-}

-- | The 'STM' action lifted into 'Edh' monad
readTMVarEdh :: forall a. TMVar a -> Edh a
readTMVarEdh = inlineSTM . readTMVar
{-# INLINE readTMVarEdh #-}

-- | The 'STM' action lifted into 'Edh' monad
takeTMVarEdh :: forall a. TMVar a -> Edh a
takeTMVarEdh = inlineSTM . takeTMVar
{-# INLINE takeTMVarEdh #-}

-- | The 'STM' action lifted into 'Edh' monad
putTMVarEdh :: forall a. TMVar a -> a -> Edh ()
putTMVarEdh ref v = inlineSTM $ putTMVar ref v
{-# INLINE putTMVarEdh #-}

-- | The 'STM' action lifted into 'Edh' monad
tryReadTMVarEdh :: forall a. TMVar a -> Edh (Maybe a)
tryReadTMVarEdh = inlineSTM . tryReadTMVar
{-# INLINE tryReadTMVarEdh #-}

-- | The 'STM' action lifted into 'Edh' monad
tryTakeTMVarEdh :: forall a. TMVar a -> Edh (Maybe a)
tryTakeTMVarEdh = inlineSTM . tryTakeTMVar
{-# INLINE tryTakeTMVarEdh #-}

-- | The 'STM' action lifted into 'Edh' monad
tryPutTMVarEdh :: forall a. TMVar a -> a -> Edh Bool
tryPutTMVarEdh ref v = inlineSTM $ tryPutTMVar ref v
{-# INLINE tryPutTMVarEdh #-}

-- | The 'IO' action lifted into 'Edh' monad
newIORefEdh :: forall a. a -> Edh (IORef a)
newIORefEdh = liftIO . newIORef
{-# INLINE newIORefEdh #-}

-- | The 'IO' action lifted into 'Edh' monad
readIORefEdh :: forall a. IORef a -> Edh a
readIORefEdh = liftIO . readIORef
{-# INLINE readIORefEdh #-}

-- | The 'IO' action lifted into 'Edh' monad
writeIORefEdh :: forall a. IORef a -> a -> Edh ()
writeIORefEdh ref v = liftIO $ writeIORef ref v
{-# INLINE writeIORefEdh #-}

-- | 'newUnique' lifted into 'Edh' monad
newUniqueEdh :: Edh Unique
-- todo: safer impl. ?
-- note: liftIO/edhContIO here will break `ai` transactions if specified by
--       scripting code, there sure be scenarios in need of new Unique id(s)
--       but too bad to sacrifice `ai`-ability
newUniqueEdh = inlineSTM $ unsafeIOToSTM newUnique
{-# INLINE newUniqueEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdCloneEdh :: forall k v. (Eq k, Hashable k) => IOPD k v -> Edh (IOPD k v)
iopdCloneEdh = inlineSTM . iopdClone
{-# INLINE iopdCloneEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdTransformEdh ::
  forall k v v'.
  (Eq k, Hashable k) =>
  (v -> v') ->
  IOPD k v ->
  Edh (IOPD k v')
iopdTransformEdh trans = inlineSTM . iopdTransform trans
{-# INLINE iopdTransformEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdEmptyEdh :: forall k v. (Eq k, Hashable k) => Edh (IOPD k v)
iopdEmptyEdh = inlineSTM iopdEmpty
{-# INLINE iopdEmptyEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdNullEdh :: forall k v. (Eq k, Hashable k) => IOPD k v -> Edh Bool
iopdNullEdh = inlineSTM . iopdNull
{-# INLINE iopdNullEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdSizeEdh :: forall k v. (Eq k, Hashable k) => IOPD k v -> Edh Int
iopdSizeEdh = inlineSTM . iopdSize
{-# INLINE iopdSizeEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdInsertEdh ::
  forall k v.
  (Eq k, Hashable k) =>
  k ->
  v ->
  IOPD k v ->
  Edh ()
iopdInsertEdh k v = inlineSTM . iopdInsert k v
{-# INLINE iopdInsertEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdReserveEdh :: forall k v. (Eq k, Hashable k) => Int -> IOPD k v -> Edh ()
iopdReserveEdh moreCap = inlineSTM . iopdReserve moreCap
{-# INLINE iopdReserveEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdUpdateEdh ::
  forall k v.
  (Eq k, Hashable k) =>
  [(k, v)] ->
  IOPD k v ->
  Edh ()
iopdUpdateEdh ps = inlineSTM . iopdUpdate ps
{-# INLINE iopdUpdateEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdLookupEdh ::
  forall k v.
  (Eq k, Hashable k) =>
  k ->
  IOPD k v ->
  Edh (Maybe v)
iopdLookupEdh key = inlineSTM . iopdLookup key
{-# INLINE iopdLookupEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdLookupDefaultEdh ::
  forall k v.
  (Eq k, Hashable k) =>
  v ->
  k ->
  IOPD k v ->
  Edh v
iopdLookupDefaultEdh v k = inlineSTM . iopdLookupDefault v k
{-# INLINE iopdLookupDefaultEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdDeleteEdh ::
  forall k v.
  (Eq k, Hashable k) =>
  k ->
  IOPD k v ->
  Edh ()
iopdDeleteEdh k = inlineSTM . iopdDelete k
{-# INLINE iopdDeleteEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdKeysEdh :: forall k v. (Eq k, Hashable k) => IOPD k v -> Edh [k]
iopdKeysEdh = inlineSTM . iopdKeys
{-# INLINE iopdKeysEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdValuesEdh :: forall k v. (Eq k, Hashable k) => IOPD k v -> Edh [v]
iopdValuesEdh = inlineSTM . iopdValues
{-# INLINE iopdValuesEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdToListEdh :: forall k v. (Eq k, Hashable k) => IOPD k v -> Edh [(k, v)]
iopdToListEdh = inlineSTM . iopdToList
{-# INLINE iopdToListEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdToReverseListEdh ::
  forall k v. (Eq k, Hashable k) => IOPD k v -> Edh [(k, v)]
iopdToReverseListEdh = inlineSTM . iopdToReverseList
{-# INLINE iopdToReverseListEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdFromListEdh ::
  forall k v.
  (Eq k, Hashable k) =>
  [(k, v)] ->
  Edh (IOPD k v)
iopdFromListEdh = inlineSTM . iopdFromList
{-# INLINE iopdFromListEdh #-}

-- | The 'IOPD' action lifted into 'Edh' monad
iopdSnapshotEdh ::
  forall k v. (Eq k, Hashable k) => IOPD k v -> Edh (OrderedDict k v)
iopdSnapshotEdh = inlineSTM . iopdSnapshot
{-# INLINE iopdSnapshotEdh #-}

-- ** Call Making & Context Manipulation

-- | Call an @Edh@ value with specified argument senders
--
-- An exception will be thrown if the callee is not actually callable
callM :: EdhValue -> [ArgSender] -> Edh EdhValue
callM callee apkr = Edh $ \_naExit -> edhMakeCall callee apkr

-- | Call an @Edh@ value with specified arguments pack
--
-- An exception will be thrown if the callee is not actually callable
callM' :: EdhValue -> ArgsPack -> Edh EdhValue
callM' callee apk = Edh $ \_naExit -> edhMakeCall' callee apk

-- | Call a magic method of an @Edh@ object with specified arguments pack
--
-- An exception will be thrown if the object does not support such magic
callMagicM :: Object -> AttrKey -> ArgsPack -> Edh EdhValue
callMagicM obj magicKey apk =
  Edh $ \_naExit -> callMagicMethod obj magicKey apk

-- | Run the specified 'Edh' action in a nested new scope
pushStackM :: Edh a -> Edh a
pushStackM !act = do
  !ets <- edhThreadState
  let !scope = edh'frame'scope $ edh'ctx'tip $ edh'context ets
  !scope' <- inlineSTM $ newNestedScope scope
  pushStackM' scope' act

-- | Run the specified 'Edh' action in a specified scope
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

-- | Evaluate an infix operator with specified lhs/rhs expression
evalInfixM :: OpSymbol -> Expr -> Expr -> Edh EdhValue
evalInfixM !opSym !lhExpr !rhExpr =
  Edh $ \_naExit -> evalInfix opSym lhExpr rhExpr

-- | Evaluate an infix operator with specified lhs/rhs expression
evalInfixSrcM :: OpSymSrc -> ExprSrc -> ExprSrc -> Edh EdhValue
evalInfixSrcM !opSym !lhExpr !rhExpr =
  Edh $ \_naExit -> evalInfixSrc opSym lhExpr rhExpr

-- ** Value Manipulations

-- | Convert an @Edh@ object to string
edhObjStrM :: Object -> Edh Text
edhObjStrM !o = Edh $ \_naExit !exit !ets ->
  edhObjStr ets o $ exitEdh ets exit

-- | Convert an @Edh@ value to string
edhValueStrM :: EdhValue -> Edh Text
edhValueStrM !v = Edh $ \_naExit !exit !ets ->
  edhValueStr ets v $ exitEdh ets exit

-- | Convert an @Edh@ object to its representation string
edhObjReprM :: Object -> Edh Text
edhObjReprM !o = Edh $ \_naExit !exit !ets ->
  edhObjRepr ets o $ exitEdh ets exit

-- | Convert an @Edh@ value to its representation string
edhValueReprM :: EdhValue -> Edh Text
edhValueReprM !v = Edh $ \_naExit !exit !ets ->
  edhValueRepr ets v $ exitEdh ets exit

-- | Convert an @Edh@ object to its descriptive string
edhObjDescM :: Object -> Edh Text
edhObjDescM !o = Edh $ \_naExit !exit !ets ->
  edhObjDesc ets o $ exitEdh ets exit

-- | Convert an @Edh@ object to its descriptive string, with auxiliary args
edhObjDescM' :: Object -> KwArgs -> Edh Text
edhObjDescM' !o !kwargs = Edh $ \_naExit !exit !ets ->
  edhObjDesc' ets o kwargs $ exitEdh ets exit

-- | Convert an @Edh@ value to its descriptive string
edhValueDescM :: EdhValue -> Edh Text
edhValueDescM !v = Edh $ \_naExit !exit !ets ->
  edhValueDesc ets v $ exitEdh ets exit

-- | Convert an @Edh@ value to its descriptive string, magics avoided
edhSimpleDescM :: EdhValue -> Edh Text
edhSimpleDescM !v = Edh $ \_naExit !exit !ets ->
  edhSimpleDesc ets v $ exitEdh ets exit

-- | Convert an @Edh@ value to its falsy value
edhValueNullM :: EdhValue -> Edh Bool
edhValueNullM !v = Edh $ \_naExit !exit !ets ->
  edhValueNull ets v $ exitEdh ets exit

-- | Convert an @Edh@ value to its JSON representation string
edhValueJsonM :: EdhValue -> Edh Text
edhValueJsonM !v = Edh $ \_naExit !exit !ets ->
  edhValueJson ets v $ exitEdh ets exit

-- | Convert an @Edh@ value to its BLOB form, alternative is requested if not
-- convertible
edhValueBlobM :: EdhValue -> Edh B.ByteString
edhValueBlobM !v = Edh $ \_naExit !exit !ets ->
  edhValueBlob ets v $ exitEdh ets exit

-- | Convert an @Edh@ value to its BLOB form, 'Nothing' is returned if not
-- convertible
edhValueBlobM' :: EdhValue -> Edh (Maybe B.ByteString)
edhValueBlobM' !v = Edh $ \_naExit !exit !ets ->
  edhValueBlob' ets v (exitEdh ets exit Nothing) $ exitEdh ets exit . Just

-- Clone a composite object with one of its object instance `mutObj` mutated
-- to bear the new object stroage
--
-- Other member instances are either deep-cloned as class based super, or left
-- intact as prototype based super
mutCloneObjectM :: Object -> Object -> ObjectStore -> Edh Object
mutCloneObjectM !endObj !mutObj !newStore = Edh $ \_naExit !exit !ets ->
  edhMutCloneObj ets endObj mutObj newStore $ exitEdh ets exit

-- Clone a composite object with one of its object instance `mutObj` mutated
-- to bear the new host storage data
--
-- Other member instances are either deep-cloned as class based super, or left
-- intact as prototype based super
--
-- todo maybe check new storage data type matches the old one?
mutCloneHostObjectM :: (Typeable h) => Object -> Object -> h -> Edh Object
mutCloneHostObjectM !endObj !mutObj =
  mutCloneObjectM endObj mutObj . HostStore . toDyn

-- | Parse an @Edh@ value as an index in @Edh@ semantics
parseEdhIndexM :: EdhValue -> Edh (Either ErrMessage EdhIndex)
parseEdhIndexM !val = Edh $ \_naExit !exit !ets ->
  parseEdhIndex ets val $ exitEdh ets exit

-- | Regulate an interger index against the actual length, similar to Python,
-- i.e. negaive value converted as if from end to beginning
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

-- | Regulate an integer slice against the actual length, similar to Python,
-- i.e. negaive value converted as if from end to beginning
regulateEdhSliceM ::
  Int -> (Maybe Int, Maybe Int, Maybe Int) -> Edh (Int, Int, Int)
regulateEdhSliceM !len !slice = Edh $ \_naExit !exit !ets ->
  regulateEdhSlice ets len slice $ exitEdh ets exit

-- ** Exceptions

-- | Throw a tagged exception with specified error message from an 'Edh' action
throwEdhM :: EdhErrorTag -> ErrMessage -> Edh a
throwEdhM tag msg = throwEdhM' tag msg []
{-# INLINE throwEdhM #-}

-- | Throw a tagged exception with specified error message, and details, from
-- an 'Edh' action
throwEdhM' :: EdhErrorTag -> ErrMessage -> [(AttrKey, EdhValue)] -> Edh a
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

-- | Throw a general exception from an 'Edh' action
throwHostM :: Exception e => e -> Edh a
throwHostM = inlineSTM . throwSTM
{-# INLINE throwHostM #-}

-- ** Artifacts Making

-- | Wrap an arbitrary Haskell value as an @Edh@ object
wrapM :: Typeable t => t -> Edh Object
wrapM t = do
  !ets <- edhThreadState
  let world = edh'prog'world $ edh'thread'prog ets
      edhWrapValue = edh'value'wrapper world Nothing
  inlineSTM $ edhWrapValue $ toDyn t

-- | Wrap an arbitrary Haskell value as an @Edh@ object, with custom type name
wrapM' :: Typeable t => Text -> t -> Edh Object
wrapM' !repr t = do
  !ets <- edhThreadState
  let world = edh'prog'world $ edh'thread'prog ets
      edhWrapValue = edh'value'wrapper world (Just repr)
  inlineSTM $ edhWrapValue $ toDyn t

-- | Wrap an arbitrary Haskell value as an @Edh@ object, with custom type name
wrapM'' :: Text -> Dynamic -> Edh Object
wrapM'' !repr !dd = do
  !ets <- edhThreadState
  let world = edh'prog'world $ edh'thread'prog ets
      edhWrapValue = edh'value'wrapper world (Just repr)
  inlineSTM $ edhWrapValue dd

-- | Create an Edh host object from the specified class and host data
--
-- note the caller is responsible to make sure the supplied host data
-- is compatible with the class
createHostObjectM :: forall t. Typeable t => Object -> t -> Edh Object
createHostObjectM !clsObj !d = createHostObjectM' clsObj (toDyn d) []

-- | Create an Edh host object from the specified class, host storage data and
-- list of super objects.
--
-- note the caller is responsible to make sure the supplied host storage data
-- is compatible with the class, the super objects are compatible with the
-- class' mro.
createHostObjectM' :: Object -> Dynamic -> [Object] -> Edh Object
createHostObjectM' !clsObj !hsd !supers = do
  !oid <- newUniqueEdh
  !ss <- newTVarEdh supers
  return $ Object oid (HostStore hsd) clsObj ss

-- | Wrap an arguments-pack taking @'Edh' 'EdhValue'@ action as an @Edh@
-- procedure
--
-- Note the args receiver is for documentation purpose only, and currently not
-- very much used.
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

-- | Use the arguments-pack taking @'Edh' ('Maybe' 'Unique', 'ObjectStore')@
-- action as the object allocator, and the @'Edh' ()@ action as class
-- initialization procedure, to create an @Edh@ class.
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

-- ** The EIO Monad

-- | Edh aware (or scriptability Enhanced) IO Monad
--
-- High density of 'liftIO's from 'Edh' monad means terrible performance
-- machine-wise, so we need this continuation based @EIO@ monad in which the
-- machine performance can be much better - 'liftIO's from within 'EIO' are
-- fairly cheaper.
--
-- You would want go deep into plain 'IO' monad, but only back to 'EIO', you
-- can 'liftEdh' to call scripted parts of the program.
--
-- CAVEAT: During either 'EIO' or plain 'IO', even though lifted from an 'Edh'
--         monad, event perceivers if any armed by the script will be suspended
--         thus unable to preempt the trunk execution, which is a desirable
--         behavior with the 'Edh' monad or 'STM' monad by 'liftSTM'.
newtype EIO a = EIO
  { -- | Run an 'EIO' action from within an @'IO' ()@ action
    --
    -- CAVEAT:
    --
    -- * You would better make sure the calling Haskell thread owns the
    --   'EdhThreadState', or the 1st transaction will be carried out in
    --   current thread, and following transactions will be carried out in
    --   the 'EdhThreadState''s owner thread, which is ridiculous. Even worse
    --   when that @Edh@ thread has already been terminated, all subsequent
    --   'STM' transactions will cease to happen, and your continuation never
    --   executed too.
    -- * Don't follow such a call with subsequent 'IO' actions, that's usually
    --   wrong. Unless interleaved "scripting threads" sharing the Haskell
    --   thread are really intended.
    --
    -- Note: This call finishes as soon with the 1st 'STM' transaction within
    --       the specified 'Edh' action, the continuation can be resumed rather
    --       later after many subsequent 'STM' transactions performed, so
    --       'catch' or similar exception handling around such calls is usually
    --        wrong.
    runEIO :: EdhThreadState -> (a -> IO ()) -> IO ()
  }

-- | Lift an 'Edh' action from an 'EIO' action
--
-- This is some similar to what @unliftio@ library does, yet better here 'Edh'
-- and 'EIO' can mutually lift eachother,
liftEdh :: Edh a -> EIO a
liftEdh act = EIO $ \ets exit ->
  atomically $ runEdh ets act $ edhContIO . exit

-- | Lift an 'EIO' action from an 'Edh' action
--
-- This is some similar to what @unliftio@ library does, yet better here 'Edh'
-- and 'EIO' can mutually lift eachother,
--
-- CAVEAT: An @ai@ block as by the scripting code will be broken, thus an
--         exception thrown, wherever any 'liftSTM' 'liftEIO' or 'liftIO' is
--         issued in execution of that block.
liftEIO :: EIO a -> Edh a
liftEIO act = Edh $ \_naExit exit ets ->
  runEdhTx ets $ edhContIO $ runEIO act ets $ atomically . exitEdh ets exit

instance Functor EIO where
  fmap f c = EIO $ \ets exit -> runEIO c ets $ exit . f
  {-# INLINE fmap #-}

instance Applicative EIO where
  pure a = EIO $ \_ets exit -> exit a
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad EIO where
  return = pure
  {-# INLINE return #-}
  m >>= k = EIO $ \ets exit -> runEIO m ets $ \a -> runEIO (k a) ets exit
  {-# INLINE (>>=) #-}

instance MonadIO EIO where
  liftIO act = EIO $ \_ets exit -> act >>= exit
  {-# INLINE liftIO #-}

-- ** EIO Monad Utilities

-- | Extract the 'EdhThreadState' from current @Edh@ thread
eioThreadState :: EIO EdhThreadState
eioThreadState = EIO $ \ets exit -> exit ets
{-# INLINE eioThreadState #-}

-- | Extract the 'EdhProgState' from current @Edh@ thread
eioProgramState :: EIO EdhProgState
eioProgramState = EIO $ \ets exit -> exit (edh'thread'prog ets)
{-# INLINE eioProgramState #-}

-- | Shorthand for @'liftIO' . 'atomically'@
atomicallyEIO :: STM a -> EIO a
atomicallyEIO = liftIO . atomically
{-# INLINE atomicallyEIO #-}

-- | The 'IO' action lifted into 'EIO' monad
newTVarEIO :: forall a. a -> EIO (TVar a)
newTVarEIO = liftIO . newTVarIO
{-# INLINE newTVarEIO #-}

-- | The 'IO' action lifted into 'EIO' monad
readTVarEIO :: forall a. TVar a -> EIO a
readTVarEIO = liftIO . readTVarIO
{-# INLINE readTVarEIO #-}

-- | The 'STM' action lifted into 'EIO' monad
writeTVarEIO :: forall a. TVar a -> a -> EIO ()
writeTVarEIO ref v = atomicallyEIO $ writeTVar ref v
{-# INLINE writeTVarEIO #-}

-- | The 'STM' action lifted into 'EIO' monad
modifyTVarEIO' :: forall a. TVar a -> (a -> a) -> EIO ()
modifyTVarEIO' ref f = atomicallyEIO $ modifyTVar' ref f
{-# INLINE modifyTVarEIO' #-}

-- | The 'IO' action lifted into 'EIO' monad
newTMVarEIO :: forall a. a -> EIO (TMVar a)
newTMVarEIO = liftIO . newTMVarIO
{-# INLINE newTMVarEIO #-}

-- | The 'STM' action lifted into 'EIO' monad
readTMVarEIO :: forall a. TMVar a -> EIO a
readTMVarEIO = atomicallyEIO . readTMVar
{-# INLINE readTMVarEIO #-}

-- | The 'STM' action lifted into 'EIO' monad
takeTMVarEIO :: forall a. TMVar a -> EIO a
takeTMVarEIO = atomicallyEIO . takeTMVar
{-# INLINE takeTMVarEIO #-}

-- | The 'STM' action lifted into 'EIO' monad
putTMVarEIO :: forall a. TMVar a -> a -> EIO ()
putTMVarEIO ref v = atomicallyEIO $ putTMVar ref v
{-# INLINE putTMVarEIO #-}

-- | The 'STM' action lifted into 'EIO' monad
tryReadTMVarEIO :: forall a. TMVar a -> EIO (Maybe a)
tryReadTMVarEIO = atomicallyEIO . tryReadTMVar
{-# INLINE tryReadTMVarEIO #-}

-- | The 'STM' action lifted into 'EIO' monad
tryTakeTMVarEIO :: forall a. TMVar a -> EIO (Maybe a)
tryTakeTMVarEIO = atomicallyEIO . tryTakeTMVar
{-# INLINE tryTakeTMVarEIO #-}

-- | The 'STM' action lifted into 'EIO' monad
tryPutTMVarEIO :: forall a. TMVar a -> a -> EIO Bool
tryPutTMVarEIO ref v = atomicallyEIO $ tryPutTMVar ref v
{-# INLINE tryPutTMVarEIO #-}

-- | The 'IO' action lifted into 'EIO' monad
newIORefEIO :: forall a. a -> EIO (IORef a)
newIORefEIO = liftIO . newIORef
{-# INLINE newIORefEIO #-}

-- | The 'IO' action lifted into 'EIO' monad
readIORefEIO :: forall a. IORef a -> EIO a
readIORefEIO = liftIO . readIORef
{-# INLINE readIORefEIO #-}

-- | The 'IO' action lifted into 'EIO' monad
writeIORefEIO :: forall a. IORef a -> a -> EIO ()
writeIORefEIO ref v = liftIO $ writeIORef ref v
{-# INLINE writeIORefEIO #-}

-- | The 'IO' action lifted into 'EIO' monad
newUniqueEIO :: EIO Unique
newUniqueEIO = liftIO newUnique
{-# INLINE newUniqueEIO #-}

-- ** Exceptions with EIO

-- | Throw a tagged exception with specified error message from an 'EIO' action
throwEIO :: EdhErrorTag -> ErrMessage -> EIO a
throwEIO tag msg = throwEIO' tag msg []
{-# INLINE throwEIO #-}

-- | Throw a tagged exception with specified error message, and details, from
-- an 'EIO' action
throwEIO' :: EdhErrorTag -> ErrMessage -> [(AttrKey, EdhValue)] -> EIO a
throwEIO' tag msg details = EIO $ \ets _exit -> do
  let !edhErr = EdhError tag msg errDetails $ getEdhErrCtx 0 ets
      !edhWrapException =
        edh'exception'wrapper (edh'prog'world $ edh'thread'prog ets)
      !errDetails = case details of
        [] -> toDyn nil
        _ -> toDyn $ EdhArgsPack $ ArgsPack [] $ odFromList details
  atomically $
    edhWrapException (Just ets) (toException edhErr)
      >>= \ !exo -> edhThrow ets $ EdhObject exo
{-# INLINE throwEIO' #-}

-- | Throw a general exception from an 'EIO' action
throwHostEIO :: Exception e => e -> EIO a
throwHostEIO = liftIO . throwIO
{-# INLINE throwHostEIO #-}
