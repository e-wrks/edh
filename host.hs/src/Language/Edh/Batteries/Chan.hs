module Language.Edh.Batteries.Chan where

-- import           Debug.Trace

import Control.Concurrent
import Control.Monad
import GHC.Conc
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.RtTypes
import Prelude

-- | operator (<-) - channel write
chanWriteProc :: EdhIntrinsicOp
chanWriteProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhChan !chan -> evalExprSrc rhExpr $ \ !rhVal ->
      writeBChan chan rhVal $ exit . EdhBool
    _ -> exitEdhTx exit edhNA

-- | virtual attribute <chan>.eos
--
-- check whether a channel is already at end-of-stream
chan'eosProc :: EdhValue -> EdhHostProc
chan'eosProc !chanVal !exit !ets =
  case edhUltimate chanVal of
    EdhChan (BChan _ !xchg) ->
      unsafeIOToSTM (tryReadMVar xchg) >>= \case
        Just BChanEOS -> exitEdh ets exit $ EdhBool True
        _ -> exitEdh ets exit $ EdhBool False
    _ -> edhSimpleDesc ets chanVal $ \ !badDesc ->
      throwEdh ets UsageError $ "not a channel but a " <> badDesc
