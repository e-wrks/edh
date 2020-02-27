
module Language.Edh.Event where

import           Prelude

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad
import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Unique

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes


-- | create a new event sink
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
launchEventProducer
  :: EdhProcExit -> EventSink -> EdhProg (STM ()) -> EdhProg (STM ())
launchEventProducer !exit sink@(EventSink _ _ _ _ !subc) !producerProg = do
  pgsConsumer <- ask
  if edh'in'tx pgsConsumer
    then throwEdh EvalError
                  "You don't launch event producers from within a transaction"
    else contEdhSTM $ do
      subcBefore <- readTVar subc
      writeTQueue
        (edh'fork'queue pgsConsumer)
        EdhTxTask
          { edh'task'pgs   = pgsConsumer
          , edh'task'wait  = True
          , edh'task'input = wuji pgsConsumer
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
                                             , edh'task'job = const producerProg
                                             }
          }
      exitEdhSTM pgsConsumer exit $ EdhSink sink


-- | publish (post) an event to a sink
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
