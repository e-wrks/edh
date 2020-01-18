
module Language.Edh.Event where

import           Prelude

import           Control.Concurrent.STM

import           Language.Edh.Details.RtTypes


-- | create a new event sink
newEventSink :: STM EventSink
newEventSink = do
  seqn <- newTVar 0
  mrv  <- newTVar nil
  chan <- newBroadcastTChan
  return EventSink { evs'seqn = seqn, evs'mrv = mrv, evs'chan = chan }

-- | subscribe to an event sink
--
-- a subscriber's channel for event reading, and the most recent event
-- value if available are returned
--
-- you can dup the broadcast channel to obtain a subscriber's channel
-- by yourself, but you risk missing the only event posted to the sink
-- if that's the case
subscribeEvents :: EventSink -> STM (TChan EdhValue, Maybe EdhValue)
subscribeEvents (EventSink seqn mrv bcc) = do
  subChan <- dupTChan bcc
  tryReadTChan subChan >>= \case
    Just ev -> return (subChan, Just ev)
    Nothing -> do
      sn <- readTVar seqn
      if sn == 0 -- no event ever posted yet
        then return (subChan, Nothing)
        else do
          lv <- readTVar mrv
          return (subChan, Just lv)

-- | publish (post) an event to a sink
publishEvent :: EventSink -> EdhValue -> STM ()
publishEvent (EventSink seqn mrv chan) val = do
  modifyTVar' seqn $ \oldSeq ->
    let newSeq = oldSeq + 1
    in  if newSeq <= 0
          -- work with int64 overflow, wrap back to 1
          then 1
          else newSeq
  writeTVar mrv val
  writeTChan chan val

