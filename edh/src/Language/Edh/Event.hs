
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

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes


-- | Create a new event sink
newEventSink :: STM EventSink
newEventSink = do
  u    <- unsafeIOToSTM newUnique
  seqn <- newTVar 0
  mrv  <- newTVar nil
  chan <- newBroadcastTChan
  subc <- newTVar 0
  return EventSink { evs'uniq = u
                   , evs'seqn = seqn
                   , evs'mrv  = mrv
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
subscribeEvents :: EventSink -> STM (TChan EdhValue, Maybe EdhValue)
subscribeEvents (EventSink _ !seqn !mrv !bcc !subc) = do
  subChan <- dupTChan bcc
  modifyTVar' subc $ \oldSubc ->
    let newSubc = oldSubc + 1
    in  if newSubc <= 0
         -- work with int64 overflow, wrap back to 1
          then 1
          else newSubc
  tryReadTChan subChan >>= \case
    Just ev -> return (subChan, Just ev)
    Nothing -> do
      sn <- readTVar seqn
      if sn == 0 -- no event ever posted yet
        then return (subChan, Nothing)
        else do
          lv <- readTVar mrv
          return (subChan, Just lv)


-- | Fork a new Edh thread to run the specified event producer, but hold the 
-- production until current thread has later started consuming events from the
-- sink returned here.
launchEventProducer :: EdhProcExit -> EventSink -> EdhProg -> EdhProg
launchEventProducer !exit sink@(EventSink _ _ _ _ !subc) !producerProg = do
  pgsConsumer <- ask
  let !pgsLaunch = pgsConsumer { edh'in'tx = False }
  contEdhSTM $ do
    subcBefore <- readTVar subc
    writeTQueue (edh'fork'queue pgsLaunch) $ Right EdhTxTask
      { edh'task'pgs   = pgsLaunch
      , edh'task'wait  = True
      , edh'task'input = wuji pgsLaunch
      , edh'task'job   = const $ do
                           pgsProducer <- ask
                           contEdhSTM $ do
                             subcNow <- readTVar subc
                             when (subcNow == subcBefore) retry
                             writeTQueue
                               (edh'task'queue pgsProducer)
                               EdhTxTask { edh'task'pgs   = pgsProducer
                                         , edh'task'wait  = False
                                         , edh'task'input = wuji pgsProducer
                                         , edh'task'job   = const producerProg
                                         }
      }
    exitEdhSTM pgsConsumer exit $ EdhSink sink


-- | Publish (post) an event to a sink
publishEvent :: EventSink -> EdhValue -> STM ()
publishEvent (EventSink _ !seqn !mrv !chan _) val = do
  modifyTVar' seqn $ \oldSeq ->
    let newSeq = oldSeq + 1
    in  if newSeq <= 0
          -- work with int64 overflow, wrap back to 1
          then 1
          else newSeq
  writeTVar mrv val
  writeTChan chan val


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
  (sink, subcBefore) <- atomically $ do
    sink <- newEventSink
    (sink, ) <$> readTVar (evs'subc sink)
  consumerThId  <- myThreadId
  _producerThId <- forkIOWithUnmask $ \unmask ->
    handle (\(e :: SomeException) -> throwTo consumerThId e) $ unmask $ do
      atomically $ do
        subcNow <- readTVar $ evs'subc sink
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
  (sink, subcBefore) <- atomically $ do
    sink <- newEventSink
    (sink, ) <$> readTVar (evs'subc sink)
  consumerDone  <- newEmptyTMVarIO
  producerThId  <- myThreadId
  _consumerThId <- forkIOWithUnmask $ \unmask ->
    flip finally (atomically $ putTMVar consumerDone ())
      $ handle (\(e :: SomeException) -> throwTo producerThId e)
      $ unmask
      $ consumingAct sink
  atomically
    $        (readTMVar consumerDone >> throwSTM
               ( UsageError "event consumer quit without subscribing to sink"
               $ EdhCallContext "<edh>" []
               )
             )
    `orElse` do
               subcNow <- readTVar $ evs'subc sink
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
  (sink, subcBefore) <- atomically $ do
    sink <- newEventSink
    (sink, ) <$> readTVar (evs'subc sink)
  producerThId  <- myThreadId
  _consumerThId <- forkIOWithUnmask $ \unmask ->
    handle (\(e :: SomeException) -> throwTo producerThId e)
      $ unmask
      $ consumingAct sink
  atomically $ do
    subcNow <- readTVar $ evs'subc sink
    when (subcNow == subcBefore) retry
  return sink

