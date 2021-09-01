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
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.RtTypes
import Prelude

-- * Monadic Interface

newtype Edh a = Edh
  { unEdh :: ([(ErrMessage, ErrContext)] -> STM ()) -> EdhTxExit a -> EdhTx
  }

mEdh :: forall a. (EdhTxExit a -> EdhTx) -> Edh a
mEdh act = Edh $ \_naExit exit -> act exit

mEdh' :: forall a. (EdhTxExit ErrMessage -> EdhTxExit a -> EdhTx) -> Edh a
mEdh' act = Edh $ \naExit exit -> do
  let naExit' :: EdhTxExit ErrMessage
      naExit' !msg !ets = naExit [(msg, getEdhErrCtx 0 ets)]
  act naExit' exit

naM :: forall a. ErrMessage -> Edh a
naM msg = mEdh' $ \naExit _exit -> naExit msg

runEdh :: EdhThreadState -> Edh a -> EdhTxExit a -> STM ()
runEdh ets ma exit = runEdhTx ets $ unEdh ma naExit exit
  where
    naExit errs =
      throwSTM $
        EdhError EvalError "No Edh action applicable" (toDyn nil) $
          T.unlines $ (\(msg, ctx) -> ctx <> "\n⛔ " <> msg) <$> errs

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

edhInlineSTM :: STM a -> Edh a
edhInlineSTM act = Edh $ \_naExit exit ets -> act >>= (`exit` ets)
{-# INLINE edhInlineSTM #-}

edhLiftSTM :: STM a -> Edh a
edhLiftSTM act = Edh $ \_naExit exit ets ->
  runEdhTx ets $
    edhContSTM $
      act >>= exitEdh ets exit
{-# INLINE edhLiftSTM #-}

liftEdhTx :: EdhTx -> Edh ()
liftEdhTx tx = Edh $ \_naExit exit ets -> tx ets >> exit () ets

instance MonadIO Edh where
  liftIO act = Edh $ \_naExit exit ets ->
    runEdhTx ets $
      edhContIO $
        act >>= atomically . exitEdh ets exit
  {-# INLINE liftIO #-}

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

readTVarEdh :: forall a. TVar a -> Edh a
readTVarEdh = edhInlineSTM . readTVar
{-# INLINE readTVarEdh #-}

writeTVarEdh :: forall a. TVar a -> a -> Edh ()
writeTVarEdh ref v = edhInlineSTM $ writeTVar ref v
{-# INLINE writeTVarEdh #-}

readIORefEdh :: forall a. IORef a -> Edh a
readIORefEdh = liftIO . readIORef
{-# INLINE readIORefEdh #-}

writeIORefEdh :: forall a. IORef a -> a -> Edh ()
writeIORefEdh ref v = liftIO $ writeIORef ref v
{-# INLINE writeIORefEdh #-}

-- ** Call Making

edhCall :: EdhValue -> [ArgSender] -> Edh EdhValue
edhCall callee args = Edh $ \_naExit -> edhMakeCall callee args

edhCall' :: EdhValue -> ArgsPack -> Edh EdhValue
edhCall' callee args = Edh $ \_naExit -> edhMakeCall' callee args

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
