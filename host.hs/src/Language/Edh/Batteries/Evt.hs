module Language.Edh.Batteries.Evt where

-- import           Debug.Trace

import Control.Concurrent.STM
import qualified Data.HashMap.Strict as Map
-- import Language.Edh.IOPD
import Language.Edh.Control
import Language.Edh.Monad
import Language.Edh.RtTypes
import Prelude

-- | operator (:-) - event deriving rule definition
evtDerivOp :: EdhIntrinsicOp
evtDerivOp _lhExpr _rhExpr !exit =
  exitEdhTx exit nil

-- | operator (-?) - event action rule definition
evtActOp :: EdhIntrinsicOp
evtActOp _lhExpr _rhExpr !exit =
  exitEdhTx exit nil

data EvtInterest = EvtInterest
  { evt'stream :: !Sink,
    evt'capture'whole :: !(Maybe Symbol),
    evt'capture'fields :: ![(AttrKey, Symbol)]
  }

data EvtStep = EvtStep
  { evt'concurrent :: ![EvtInterest],
    evt'step'guard :: !(Maybe (Edh Bool))
  }

data EvtRule = EvtRule
  { evt'match'seq :: ![EvtStep],
    evt'incidents ::
      !( TVar
           ( Map.HashMap EvtFabrics EvtIncident,
             Map.HashMap Sink [EvtIncident]
           )
       )
  }

-- | Common attribute keys & values the fabrication of one specific rule match
-- must hold.
--
-- Only symbols appeared in more than one upstream event capture are considered
-- common attribute.
newtype EvtFabrics = EvtFabrics (Map.HashMap Symbol EdhValue)

-- | All attribute keys & values one specific rule match is evaluated against.
--
-- Including all symbols appeared in any upstream event capture.
newtype EvtContext = EvtContext (Map.HashMap Symbol EdhValue)

-- | In-progress (or including finished?) fabrication (matching) of a rule.
--
-- Incidents with same 'EvtFabrics' are mutually exclusive.
data EvtIncident = EvtIncident
  { evt'curr'match :: !EvtFabrics,
    evt'curr'step :: !EvtStep,
    evt'missing :: ![EvtInterest],
    evt'subseqs :: ![EvtStep],
    evt'context :: !EvtContext
  }

perceiveEvt :: EvtRule -> Edh () -> Sink -> Object -> Edh ()
perceiveEvt (EvtRule [] _) _ _ _ = throwEdhM EvalError "empty event rule"
perceiveEvt (EvtRule mseq@(step1 : subseqs) !inciVar) !act !evs !evo = do
  return ()
  where
    matchEvt :: EvtIncident -> Edh (Maybe EvtIncident)
    matchEvt !inci =
      return Nothing
