module Language.Edh.Batteries.Evt where

-- import           Debug.Trace

import Control.Concurrent.STM
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.RtTypes
import Prelude

-- | operator (<-) - event publisher
evtPubProc :: EdhIntrinsicOp
evtPubProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhSink !es -> evalExprSrc rhExpr $
      \ !rhVal ->
        let -- allow special values to be published, e.g. {break}
            !val2Pub = edhDeCaseWrap rhVal
            -- but shield those special values for the result of this op, or it
            -- can be interpreted the same as such a value standalone, which
            -- would implement wrong semantics.
            !val2Rtn = edhDeFlowCtrl val2Pub
         in postEdhEvent es val2Pub $ \() -> exitEdhTx exit val2Rtn
    _ -> exitEdhTx exit edhNA

-- | virtual attribute <sink>.subseq
--
-- obtain a non-lingering, shadow copy of the event sink
sink'subseqProc :: EdhValue -> EdhHostProc
sink'subseqProc !sinkVal !exit !ets =
  case edhUltimate sinkVal of
    EdhSink !sink -> exitEdh ets exit $ EdhSink sink {sink'mrv = Nothing}
    _ -> edhSimpleDesc ets sinkVal $ \ !badDesc ->
      throwEdh ets UsageError $ "not an event sink but a " <> badDesc

-- | virtual attribute <sink>.mrv
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
sink'mrvProc :: EdhValue -> EdhHostProc
sink'mrvProc !sinkVal !exit !ets =
  case edhUltimate sinkVal of
    EdhSink !sink -> case sink'mrv sink of
      Nothing -> exitEdh ets exit nil
      Just !mrvv -> readTVar mrvv >>= \ !mrv -> exitEdh ets exit mrv
    _ -> edhSimpleDesc ets sinkVal $ \ !badDesc ->
      throwEdh ets UsageError $ "not an event sink but a " <> badDesc

-- | virtual attribute <sink>.eos
--
-- check whether an event sink is already at end-of-stream
sink'eosProc :: EdhValue -> EdhHostProc
sink'eosProc !sinkVal !exit !ets =
  case edhUltimate sinkVal of
    EdhSink !sink ->
      readTVar (sink'subc sink)
        >>= \ !subc -> exitEdh ets exit $ EdhBool $ subc < 0
    _ -> edhSimpleDesc ets sinkVal $ \ !badDesc ->
      throwEdh ets UsageError $ "not an event sink but a " <> badDesc
