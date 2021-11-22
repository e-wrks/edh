module Language.Edh.Sink where

-- import           Debug.Trace

import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.Dynamic
import Language.Edh.Control
import Language.Edh.RUID
import Language.Edh.RtTypes
import Prelude

-- | Create a new lingering event sink
newSink :: STM Sink
newSink = newSink' True

-- | Create a new event sink with lingering or not specified
newSink' :: Bool -> STM Sink
newSink' !lingering = do
  !u <- newRUID'STM
  !mrv <-
    if lingering
      then Just <$> newTVar nil
      else return Nothing
  !chan <- newBroadcastTChan
  !atomsVar <- newTVar $ const $ return ()
  !subc <- newTVar 0
  return
    Sink
      { sink'uniq = u,
        sink'mrv = mrv,
        sink'chan = chan,
        sink'atoms = atomsVar,
        sink'subc = subc
      }

-- | Subscribe to an event sink
--
-- A subscriber's channel for event reading, and the most recent event
-- value if available are returned
--
-- CAVEAT: should not by other means be dup'ing the broadcast channel,
--         to obtain a subscriber's channel.
subscribeEvents :: Sink -> STM (Maybe (TChan EdhValue, Maybe EdhValue))
subscribeEvents (Sink _ !mrv !bcc _ !subc) =
  readTVar subc >>= \ !oldSubc ->
    if oldSubc < 0
      then return Nothing
      else do
        writeTVar subc $ -- work with int64 overflow, wrap back to 1
          let !newSubc = oldSubc + 1 in if newSubc <= 0 then 1 else newSubc
        !subChan <- dupTChan bcc
        case mrv of
          Nothing -> return $ Just (subChan, Nothing)
          Just !mrvv ->
            readTVar mrvv >>= \case
              EdhNil -> return $ Just (subChan, Nothing)
              !ev -> return $ Just (subChan, Just ev)

-- | Post an event into a sink
postEvent :: Sink -> EdhValue -> STM Bool
postEvent (Sink _ !mrv !chan !atomsVar !subc) !val =
  readTVar subc >>= \ !oldSubc ->
    if oldSubc < 0
      then return False
      else do
        writeTChan chan val
        case mrv of
          Nothing -> pure ()
          Just !mrvv -> writeTVar mrvv val
        when (val == EdhNil) $ writeTVar subc (-1) -- mark end-of-stream
        !atoms <- readTVar atomsVar
        atoms val
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
forkEventProducer :: Maybe Sink -> (Sink -> IO ()) -> IO Sink
forkEventProducer !reuseEdhSink !producingAct = do
  (!sink, !subcBefore) <- atomically $ do
    !sink <- maybe newSink return reuseEdhSink
    (sink,) <$> readTVar (sink'subc sink)
  !consumerThId <- myThreadId
  _producerThId <- forkIOWithUnmask $ \unmask ->
    handle (\(e :: SomeException) -> throwTo consumerThId e) $
      unmask $ do
        atomically $ do
          !subcNow <- readTVar $ sink'subc sink
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
forkEventConsumer :: Maybe Sink -> (Sink -> IO ()) -> IO Sink
forkEventConsumer !reuseEdhSink !consumingAct = do
  (!sink, !subcBefore) <- atomically $ do
    !sink <- maybe newSink return reuseEdhSink
    (sink,) <$> readTVar (sink'subc sink)
  !consumerDone <- newEmptyTMVarIO
  !producerThId <- myThreadId
  _consumerThId <- forkIOWithUnmask $ \unmask ->
    flip finally (atomically $ putTMVar consumerDone ()) $
      handle (\(e :: SomeException) -> throwTo producerThId e) $
        unmask $
          consumingAct sink
  atomically $
    ( readTMVar consumerDone
        >> throwSTM
          ( EdhError
              UsageError
              "event consumer quit without subscribing to sink"
              (toDyn nil)
              "<edh>"
          )
    )
      `orElse` do
        !subcNow <- readTVar $ sink'subc sink
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
waitEventConsumer :: Maybe Sink -> (Sink -> IO ()) -> IO Sink
waitEventConsumer !reuseEdhSink !consumingAct = do
  (!sink, !subcBefore) <- atomically $ do
    !sink <- maybe newSink return reuseEdhSink
    (sink,) <$> readTVar (sink'subc sink)
  !producerThId <- myThreadId
  _consumerThId <- forkIOWithUnmask $ \unmask ->
    handle (\(e :: SomeException) -> throwTo producerThId e) $
      unmask $
        consumingAct sink
  atomically $ do
    !subcNow <- readTVar $ sink'subc sink
    when (subcNow == subcBefore) retry
  return sink
