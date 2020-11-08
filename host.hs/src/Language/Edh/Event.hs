
module Language.Edh.Event where

import           Prelude
-- import           Debug.Trace
-- import           System.IO.Unsafe

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Exception
import           Control.Monad.Reader

import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Unique
import           Data.Dynamic

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes


-- | Create a new event sink
newEventSink :: STM EventSink
newEventSink = do
  !u    <- unsafeIOToSTM newUnique
  !mrv  <- newTVar nil
  !chan <- newBroadcastTChan
  !subc <- newTVar 0
  return EventSink { evs'uniq = u
                   , evs'mrv  = Just mrv
                   , evs'chan = chan
                   , evs'subc = subc
                   }


-- | Subscribe to an event sink
--
-- A subscriber's channel for event reading, and the most recent event
-- value if available are returned
--
-- CAVEAT: should not by other means be dup'ing the broadcast channel,
--         to obtain a subscriber's channel.
subscribeEvents :: EventSink -> STM (Maybe (TChan EdhValue, Maybe EdhValue))
subscribeEvents (EventSink _ !mrv !bcc !subc) =
  readTVar subc >>= \ !oldSubc -> if oldSubc < 0
    then return Nothing
    else do
      writeTVar subc -- work with int64 overflow, wrap back to 1
        $ let !newSubc = oldSubc + 1 in if newSubc <= 0 then 1 else newSubc
      !subChan <- dupTChan bcc
      case mrv of
        Nothing    -> return $ Just (subChan, Nothing)
        Just !mrvv -> readTVar mrvv >>= \case
          EdhNil -> return $ Just (subChan, Nothing)
          !ev    -> return $ Just (subChan, Just ev)


-- | Post an event into a sink
postEvent :: EventSink -> EdhValue -> STM Bool
postEvent (EventSink _ !mrv !chan !subc) !val =
  readTVar subc >>= \ !oldSubc -> if oldSubc < 0
    then return False
    else do
      writeTChan chan val
      case mrv of
        Nothing    -> pure ()
        Just !mrvv -> writeTVar mrvv val
      when (val == EdhNil) $ writeTVar subc (-1) -- mark end-of-stream
      return True


-- | Fork a new thread to do event producing, with current thread assumed
-- to do event consuming subsequently.
--
-- The producing action will only start after the event sink is subscribed
-- (presumably from subsequent actions in current thread).
--
-- Any exception occurs in the producing action will be propagated to
-- current thread as an asynchronous exception.
--
-- CAVEAT: if the returned sink is never subscribed before current thread
--         exits, it'll be detected as stm deadlock and your process may
--         get killed.
forkEventProducer :: (EventSink -> IO ()) -> IO EventSink
forkEventProducer !producingAct = do
  (!sink, !subcBefore) <- atomically $ do
    !sink <- newEventSink
    (sink, ) <$> readTVar (evs'subc sink)
  !consumerThId <- myThreadId
  _producerThId <- forkIOWithUnmask $ \unmask ->
    handle (\(e :: SomeException) -> throwTo consumerThId e) $ unmask $ do
      atomically $ do
        !subcNow <- readTVar $ evs'subc sink
        when (subcNow == subcBefore) retry
      producingAct sink
  return sink


-- | Fork a new thread to do event consuming, with current thread assumed
-- to do event producing subsequently.
--
-- This function will block until the event sink is subscribed (presumably
-- from the consuming action in the new thread)
--
-- Any exception occurs in the consuming action will be propagated to
-- current thread as an asynchronous exception.
forkEventConsumer :: (EventSink -> IO ()) -> IO EventSink
forkEventConsumer !consumingAct = do
  (!sink, !subcBefore) <- atomically $ do
    !sink <- newEventSink
    (sink, ) <$> readTVar (evs'subc sink)
  !consumerDone <- newEmptyTMVarIO
  !producerThId <- myThreadId
  _consumerThId <- forkIOWithUnmask $ \unmask ->
    flip finally (atomically $ putTMVar consumerDone ())
      $ handle (\(e :: SomeException) -> throwTo producerThId e)
      $ unmask
      $ consumingAct sink
  atomically
    $        (readTMVar consumerDone >> throwSTM
               ( EdhError UsageError
                          "event consumer quit without subscribing to sink"
                          (toDyn nil)
               $ EdhCallContext "<edh>" []
               )
             )
    `orElse` do
               !subcNow <- readTVar $ evs'subc sink
               when (subcNow == subcBefore) retry
  return sink


-- | Wait asynchronous event consumer subscribed, with current thread assumed
-- to do event producing subsequently.
--
-- This function will block until the event sink is subscribed (presumably
-- triggered asynchronously by the consuming action)
--
-- Any exception occurs in the consuming action will be propagated to
-- current thread as an asynchronous exception.
--
-- CAVEAT: if the returned sink is never subscribed by any thread seen it,
--         it'll be detected as stm deadlock and your process may
--         get killed.
waitEventConsumer :: (EventSink -> IO ()) -> IO EventSink
waitEventConsumer !consumingAct = do
  (!sink, !subcBefore) <- atomically $ do
    !sink <- newEventSink
    (sink, ) <$> readTVar (evs'subc sink)
  !producerThId <- myThreadId
  _consumerThId <- forkIOWithUnmask $ \unmask ->
    handle (\(e :: SomeException) -> throwTo producerThId e)
      $ unmask
      $ consumingAct sink
  atomically $ do
    !subcNow <- readTVar $ evs'subc sink
    when (subcNow == subcBefore) retry
  return sink

