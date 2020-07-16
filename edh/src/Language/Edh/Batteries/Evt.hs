
module Language.Edh.Batteries.Evt where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.Reader

import           Control.Concurrent.STM

import qualified Data.Text                     as T

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | utility mre()
--
-- get most-recent-event from a sink without blocking
--
-- this can't tell a sink's state as marked end-of-stream by a nil data,
-- or no event has ever been posted into it, in both cases `mre()` will
-- return nil
mreProc :: EdhProcedure
mreProc (ArgsPack !args !kwargs) !exit = case args of
  [v] | compactDictNull kwargs -> case edhUltimate v of
    EdhSink !sink -> ask >>= \pgs ->
      contEdhSTM $ readTVar (evs'mrv sink) >>= \mrv -> exitEdhSTM pgs exit mrv
    _ ->
      throwEdh EvalError $ "mre() expects an event sink but passed a " <> T.pack
        (edhTypeNameOf v)
  _ -> throwEdh UsageError "Invalid arg to mre()"


-- | utility eos()
--
-- check whether an event sink is already at end-of-stream, which is marked
-- by a nil data
eosProc :: EdhProcedure
eosProc (ArgsPack !args !kwargs) !exit = case args of
  [v] | compactDictNull kwargs -> case edhUltimate v of
    EdhSink !sink -> ask >>= \pgs ->
      contEdhSTM $ readTVar (evs'seqn sink) >>= \case
        0 -> exitEdhSTM pgs exit $ EdhBool False
        _ -> readTVar (evs'mrv sink) >>= \case
          EdhNil -> exitEdhSTM pgs exit $ EdhBool True
          _      -> exitEdhSTM pgs exit $ EdhBool False
    _ ->
      throwEdh EvalError $ "eos() expects an event sink but passed a " <> T.pack
        (edhTypeNameOf v)
  _ -> throwEdh UsageError "Invalid arg to eos()"

