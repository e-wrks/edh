
module Language.Edh.Batteries.Reflect where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Concurrent.STM

import qualified Data.Text                     as T
import           Data.Unique

import           Language.Edh.Control
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | utility constructor(*args,**kwargs)
ctorProc :: EdhHostProc
ctorProc (ArgsPack !args !kwargs) !exit !ets = do
  if odNull kwargs
    then case argsCls of
      [] ->
        exitEdhSTM ets exit $ EdhObject $ edh'obj'class $ edh'scope'this scope
      [t] -> exitEdhSTM ets exit t
      _   -> exitEdhSTM ets exit $ EdhArgsPack $ ArgsPack argsCls odEmpty
    else exitEdhSTM ets
                    exit
                    (EdhArgsPack $ ArgsPack argsCls $ odMap edhClassOf kwargs)
 where
  !ctx     = edh'context ets
  !scope   = contextScope ctx

  !argsCls = edhClassOf <$> args

  edhClassOf :: EdhValue -> EdhValue
  edhClassOf (EdhObject !o) = EdhObject $ edh'obj'class o
  edhClassOf _              = edhNone

-- | utility supers(*args,**kwargs)
supersProc :: EdhHostProc
supersProc (ArgsPack !args !kwargs) !exit !ets = do
  if null args && odNull kwargs
    then do
      !supers <-
        map EdhObject <$> (readTVar $ edh'obj'supers $ edh'scope'this scope)
      exitEdhSTM ets exit $ EdhArgsPack $ ArgsPack supers odEmpty
    else if odNull kwargs
      then do
        !argsSupers <- sequence $ supersOf <$> args
        case argsSupers of
          [v] -> exitEdhSTM ets exit v
          _   -> exitEdhSTM ets exit $ EdhArgsPack $ ArgsPack argsSupers odEmpty
      else do
        !argsSupers   <- sequence $ supersOf <$> args
        !kwargsSupers <- odMapSTM supersOf kwargs
        exitEdhSTM ets exit (EdhArgsPack $ ArgsPack argsSupers kwargsSupers)
 where
  !ctx   = edh'context ets
  !scope = contextScope ctx

  supersOf :: EdhValue -> STM EdhValue
  supersOf !v = case v of
    EdhObject !o ->
      map EdhObject <$> readTVar (edh'obj'supers o) >>= \ !supers ->
        return $ EdhArgsPack $ ArgsPack supers odEmpty
    _ -> return edhNone


-- | utility makeOp(lhExpr, opSym, rhExpr)
makeOpProc :: EdhHostProc
makeOpProc (ArgsPack !args !kwargs) !exit = if (not $ odNull kwargs)
  then throwEdhTx EvalError "No kwargs accepted by makeOp"
  else case args of
    [(EdhExpr _ !lhe _), EdhString !op, (EdhExpr _ !rhe _)] -> \ !ets -> do
      !xu <- unsafeIOToSTM newUnique
      exitEdhSTM ets exit $ EdhExpr xu (InfixExpr op lhe rhe) ""
    _ -> throwEdhTx EvalError $ "Invalid arguments to makeOp: " <> T.pack
      (show args)

