
module Language.Edh.Batteries.Evt where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import           Language.Edh.Details.RtTypes


-- | utility mre()
--
-- get most-recent-event from a sink without blocking
--
-- this can't tell a sink's state as marked end-of-stream by a nil data,
-- or no event has ever been posted into it, in both cases `mre()` will
-- return nil
mreProc :: EventSink -> EdhHostProc
mreProc !sink !exit !ets =
  readTVar (evs'mrv sink) >>= \ !mrv -> exitEdh ets exit mrv


-- | utility eos()
--
-- check whether an event sink is already at end-of-stream, which is marked
-- by a nil data
eosProc :: EventSink -> EdhHostProc
eosProc !sink !exit !ets = readTVar (evs'seqn sink) >>= \case
  0 -> exitEdh ets exit $ EdhBool False
  _ -> readTVar (evs'mrv sink) >>= \case
    EdhNil -> exitEdh ets exit $ EdhBool True
    _      -> exitEdh ets exit $ EdhBool False

