
module Language.Edh.Batteries.Reflect where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad

import           Control.Concurrent.STM

import qualified Data.Text                     as T
import           Data.Unique

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
  case edh'obj'store nsClsObj of
    ClassStore !nsCls -> case edhClassName nsClsObj of
      "_"     -> throwEdh ets UsageError "anonymous sandbox is not reasonable"
      !sbName -> do
        let
          !nsProc = edh'class'proc nsCls
          !sbVal  = EdhObject nsObject
            { edh'obj'class = nsClsObj
              { edh'obj'store = ClassStore nsCls
                { edh'class'proc = nsProc
                                     { edh'procedure'lexi = edh'world'sandbox
                                                              world
                                     }
                }
              }
            }
        unless (edh'ctx'pure ctx) $ iopdInsert
          (AttrByName sbName)
          sbVal
          (edh'scope'entity $ contextScope ctx)
        exitEdh ets exit sbVal
    _ -> throwEdh ets EvalError "bug: class object not bearing ClassStore"
 where
  !ctx      = edh'context ets
  !world    = edh'ctx'world ctx
  !nsClsObj = edh'obj'class nsObject


-- | utility makeOp(lhExpr, opSym, rhExpr)
makeOpProc :: [EdhValue] -> EdhHostProc
makeOpProc !args !exit = case args of
  [(EdhExpr _ !lhe _), EdhString !op, (EdhExpr _ !rhe _)] -> \ !ets -> do
    !xu <- unsafeIOToSTM newUnique
    exitEdh ets exit $ EdhExpr xu (InfixExpr op lhe rhe) ""
  _ -> throwEdhTx EvalError $ "invalid arguments to makeOp: " <> T.pack
    (show args)

