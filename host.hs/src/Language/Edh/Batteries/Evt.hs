module Language.Edh.Batteries.Evt where

-- import           Debug.Trace

import Language.Edh.RtTypes

-- | operator (:-) - event deriving rule definition
evtDerivOp :: EdhIntrinsicOp
evtDerivOp _lhExpr _rhExpr !exit =
  exitEdhTx exit nil

-- | operator (-?) - event action rule definition
evtActOp :: EdhIntrinsicOp
evtActOp _lhExpr _rhExpr !exit =
  exitEdhTx exit nil
