
module Language.Edh.Batteries.Evt where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import           Language.Edh.Args
import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | virtual property <sink>.subseq
--
-- obtain a non-lingering, shadow copy of the event sink
sink'subseqProc :: "sinkValue" !: EdhValue -> EdhHostProc
sink'subseqProc (mandatoryArg -> !sinkVal) !exit !ets =
  case edhUltimate sinkVal of
    EdhSink !sink -> exitEdh ets exit $ EdhSink sink { evs'mrv = Nothing }
    _             -> edhValueDesc ets sinkVal $ \ !badDesc ->
      throwEdh ets UsageError $ "not an event sink but a " <> badDesc


-- | virtual property <sink>.mrv
--
-- get most recent event value from a sink, without blocking
--
-- when `nil` is returned, the case can be:
--   *) the sink is already at eos (end-of-stream)
--   *) the sink is a non-lingering copy
--   *) the sink is a lingering copy, but no event value has ever been
--      published into it
--
-- NOTE
--   a non-lingering copy of a sink will always return `nil` as its `.mrv`
--
sink'mrvProc :: "sinkValue" !: EdhValue -> EdhHostProc
sink'mrvProc (mandatoryArg -> !sinkVal) !exit !ets =
  case edhUltimate sinkVal of
    EdhSink !sink -> case evs'mrv sink of
      Nothing    -> exitEdh ets exit nil
      Just !mrvv -> readTVar mrvv >>= \ !mrv -> exitEdh ets exit mrv
    _ -> edhValueDesc ets sinkVal $ \ !badDesc ->
      throwEdh ets UsageError $ "not an event sink but a " <> badDesc


-- | virtual property <sink>.eos
--
-- check whether an event sink is already at end-of-stream
sink'eosProc :: "sinkValue" !: EdhValue -> EdhHostProc
sink'eosProc (mandatoryArg -> !sinkVal) !exit !ets =
  case edhUltimate sinkVal of
    EdhSink !sink -> readTVar (evs'subc sink)
      >>= \ !subc -> exitEdh ets exit $ EdhBool $ subc < 0
    _ -> edhValueDesc ets sinkVal $ \ !badDesc ->
      throwEdh ets UsageError $ "not an event sink but a " <> badDesc

