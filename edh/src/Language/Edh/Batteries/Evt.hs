
module Language.Edh.Batteries.Evt where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.Reader

import           Control.Concurrent.STM

import qualified Data.Text                     as T

import           Language.Edh.Control
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | utility mre()
--
-- get most-recent-event from a sink without blocking
--
-- this can't tell a sink's state as marked end-of-stream by a nil data,
-- or no event has ever been posted into it, in both cases `mre()` will
-- return nil
mreProc :: EdhHostProc
mreProc (ArgsPack !args !kwargs) !exit = case args of
  [v] | odNull kwargs -> case edhUltimate v of
    EdhSink !sink -> ask >>= \ets ->
      contEdhSTM $ readTVar (evs'mrv sink) >>= \mrv -> exitEdh ets exit mrv
    _ ->
      throwEdh EvalError $ "mre() expects an event sink but passed a " <> T.pack
        (edhTypeNameOf v)
  _ -> throwEdh UsageError "invalid arg to mre()"


-- | utility eos()
--
-- check whether an event sink is already at end-of-stream, which is marked
-- by a nil data
eosProc :: EdhHostProc
eosProc (ArgsPack !args !kwargs) !exit = case args of
  [v] | odNull kwargs -> case edhUltimate v of
    EdhSink !sink -> ask >>= \ets ->
      contEdhSTM $ readTVar (evs'seqn sink) >>= \case
        0 -> exitEdh ets exit $ EdhBool False
        _ -> readTVar (evs'mrv sink) >>= \case
          EdhNil -> exitEdh ets exit $ EdhBool True
          _      -> exitEdh ets exit $ EdhBool False
    _ ->
      throwEdh EvalError $ "eos() expects an event sink but passed a " <> T.pack
        (edhTypeNameOf v)
  _ -> throwEdh UsageError "invalid arg to eos()"

