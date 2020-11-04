
module Language.Edh.Batteries.Reflect where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad
import           Control.Exception

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Unique
import           Data.Dynamic

import           Text.Megaparsec

import           Language.Edh.Control
import           Language.Edh.Args
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | utility constructor(*args,**kwargs)
ctorProc :: ArgsPack -> EdhHostProc
ctorProc (ArgsPack !args !kwargs) !exit !ets = do
  if odNull kwargs
    then case argsCls of
      []  -> exitEdh ets exit $ EdhObject $ edh'obj'class $ edh'scope'this scope
      [t] -> exitEdh ets exit t
      _   -> exitEdh ets exit $ EdhArgsPack $ ArgsPack argsCls odEmpty
    else exitEdh ets
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
supersProc :: ArgsPack -> EdhHostProc
supersProc (ArgsPack !args !kwargs) !exit !ets = do
  if null args && odNull kwargs
    then do
      !supers <-
        map EdhObject <$> (readTVar $ edh'obj'supers $ edh'scope'this scope)
      exitEdh ets exit $ EdhArgsPack $ ArgsPack supers odEmpty
    else if odNull kwargs
      then do
        !argsSupers <- sequence $ supersOf <$> args
        case argsSupers of
          [v] -> exitEdh ets exit v
          _   -> exitEdh ets exit $ EdhArgsPack $ ArgsPack argsSupers odEmpty
      else do
        !argsSupers   <- sequence $ supersOf <$> args
        !kwargsSupers <- odMapSTM supersOf kwargs
        exitEdh ets exit (EdhArgsPack $ ArgsPack argsSupers kwargsSupers)
 where
  !ctx   = edh'context ets
  !scope = contextScope ctx

  supersOf :: EdhValue -> STM EdhValue
  supersOf !v = case v of
    EdhObject !o ->
      map EdhObject <$> readTVar (edh'obj'supers o) >>= \ !supers ->
        return $ EdhArgsPack $ ArgsPack supers odEmpty
    _ -> return edhNone


-- | utility sandbox(nsObject) - transform a vanilla namespace object into a
-- sandbox object. 
--
-- idiomatic usage: 
--
--    sandbox$
--    namespace name'of'the'sandbox( ... ) {
--      ...
--    }
--
-- the sandbox object will retain the identity of the original object, while its
-- class procedure's lexcical scope will be changed to the world's sandbox scope
-- so as for reflective scopes created from it to have their outer scopes be the
-- world's sandbox scope.
sandboxProc :: "nsObject" !: Object -> EdhHostProc
sandboxProc (mandatoryArg -> nsObject) !exit !ets =
  mkSandbox ets nsObject $ \ !sbScope -> case objClassName nsObject of
    "_"     -> throwEdh ets UsageError "anonymous sandbox is not reasonable"
    !sbName -> do
      let !sbVal = EdhObject $ edh'scope'this sbScope
      unless (edh'ctx'pure ctx) $ iopdInsert
        (AttrByName sbName)
        sbVal
        (edh'scope'entity $ contextScope ctx)
      exitEdh ets exit sbVal
  where !ctx = edh'context ets


-- | utility makeOp(lhExpr, opSym, rhExpr)
makeOpProc :: [EdhValue] -> EdhHostProc
makeOpProc !args !exit = case args of
  [(EdhExpr _ !lhe _), EdhString !op, (EdhExpr _ !rhe _)] -> \ !ets -> do
    !xu <- unsafeIOToSTM newUnique
    exitEdh ets exit $ EdhExpr xu (InfixExpr op lhe rhe) ""
  _ -> throwEdhTx EvalError $ "invalid arguments to makeOp: " <> T.pack
    (show args)


-- | utility parseEdh(srcCode, srcName='<edh>', lineNo=1)
parseEdhProc
  :: "srcCode" !: Text -> "srcName" ?: Text -> "lineNo" ?: Int -> EdhHostProc
parseEdhProc (mandatoryArg  -> !srcCode) (defaultArg  "<edh>"  -> !srcName) (defaultArg  1 -> !lineNo) !exit !ets
  = parseEdh' world (T.unpack srcName) lineNo srcCode >>= \case
    Left !err -> do
      let !msg = T.pack $ errorBundlePretty err
          !edhWrapException =
            edh'exception'wrapper (edh'ctx'world $ edh'context ets)
          !cc     = getEdhCallContext 0 ets
          !edhErr = EdhError ParseError msg (toDyn nil) cc
      edhWrapException (toException edhErr)
        >>= \ !exo -> edhThrow ets (EdhObject exo)
    Right (!stmts, _docCmt) -> do
      !u <- unsafeIOToSTM newUnique
      exitEdh ets exit $ EdhExpr u (BlockExpr stmts) srcCode
 where
  ctx   = edh'context ets
  world = edh'ctx'world ctx
