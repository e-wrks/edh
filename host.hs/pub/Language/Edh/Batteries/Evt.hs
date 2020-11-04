
module Language.Edh.Batteries.Evt where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import           Language.Edh.Args
import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | virtual property <sink>.mrv
--
-- get most-recent-event from a sink without blocking
--
-- this can't tell a sink's state as marked end-of-stream by a nil data,
-- or no event has ever been posted into it, in both cases this will
-- return nil
sink'mrvProc :: "sinkValue" !: EdhValue -> EdhHostProc
sink'mrvProc (mandatoryArg -> !sinkVal) !exit !ets =
  case edhUltimate sinkVal of
    EdhSink !sink -> readTVar (evs'mrv sink) >>= \ !mrv -> exitEdh ets exit mrv
    _             -> edhValueDesc ets sinkVal $ \ !badDesc ->
      throwEdh ets UsageError $ "not an event sink but a " <> badDesc


-- | virtual property <sink>.eos
--
-- check whether an event sink is already at end-of-stream, which is marked
-- by a nil data
sink'eosProc :: "sinkValue" !: EdhValue -> EdhHostProc
sink'eosProc (mandatoryArg -> !sinkVal) !exit !ets =
  case edhUltimate sinkVal of
    EdhSink !sink -> readTVar (evs'seqn sink) >>= \case
      0 -> exitEdh ets exit $ EdhBool False
      _ -> readTVar (evs'mrv sink) >>= \case
        EdhNil -> exitEdh ets exit $ EdhBool True
        _      -> exitEdh ets exit $ EdhBool False
    _ -> edhValueDesc ets sinkVal $ \ !badDesc ->
      throwEdh ets UsageError $ "not an event sink but a " <> badDesc

