
module Language.Edh.Batteries.Evt where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.Reader

import           Control.Concurrent.STM

import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

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
  [v] | Map.null kwargs -> case edhUltimate v of
    EdhSink !sink -> ask >>= \pgs ->
      contEdhSTM $ readTVar (evs'mrv sink) >>= \mrv -> exitEdhSTM pgs exit mrv
    _ ->
      throwEdh EvalError $ "mre() expects an event sink but passed a " <> T.pack
        (edhTypeNameOf v)
  _ -> throwEdh UsageError "Invalid arg to mre()"

