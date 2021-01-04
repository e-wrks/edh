module Language.Edh.Batteries.Reflect where

-- import           Debug.Trace

import Control.Concurrent.STM (STM, readTVar)
import Control.Exception (Exception (toException))
import Control.Monad (unless)
import Data.Dynamic (fromDynamic, toDyn)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Unique (newUnique)
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Args
  ( defaultArg,
    mandatoryArg,
    type (!:),
    type (?:),
  )
import Language.Edh.Control
  ( EdhError (EdhError),
    EdhErrorTag (EvalError, ParseError, UsageError),
    noSrcRange,
  )
import Language.Edh.Evaluate
  ( edhThrow,
    getEdhErrCtx,
    mkObjSandbox,
    mkScopeSandbox,
    parseEdh',
    throwEdh,
    throwEdhTx,
  )
import Language.Edh.IOPD
  ( iopdInsert,
    odEmpty,
    odMap,
    odMapSTM,
    odNull,
  )
import Language.Edh.RtTypes
import Text.Megaparsec (errorBundlePretty)
import Prelude

-- | utility constructor(*args,**kwargs)
ctorProc :: ArgsPack -> EdhHostProc
ctorProc (ArgsPack !args !kwargs) !exit !ets = do
  if odNull kwargs
    then case argsCls of
      [] -> exitEdh ets exit $ EdhObject $ edh'obj'class $ edh'scope'this scope
      [t] -> exitEdh ets exit t
      _ -> exitEdh ets exit $ EdhArgsPack $ ArgsPack argsCls odEmpty
    else
      exitEdh
        ets
        exit
        (EdhArgsPack $ ArgsPack argsCls $ odMap edhClassOf kwargs)
  where
    !ctx = edh'context ets
    !scope = contextScope ctx

    !argsCls = edhClassOf <$> args

    edhClassOf :: EdhValue -> EdhValue
    edhClassOf (EdhObject !o) = EdhObject $ edh'obj'class o
    edhClassOf _ = edhNone

-- | utility supers(*args,**kwargs)
supersProc :: ArgsPack -> EdhHostProc
supersProc (ArgsPack !args !kwargs) !exit !ets = do
  if null args && odNull kwargs
    then do
      !supers <-
        map EdhObject <$> readTVar (edh'obj'supers $ edh'scope'this scope)
      exitEdh ets exit $ EdhArgsPack $ ArgsPack supers odEmpty
    else
      if odNull kwargs
        then do
          !argsSupers <- sequence $ supersOf <$> args
          case argsSupers of
            [v] -> exitEdh ets exit v
            _ -> exitEdh ets exit $ EdhArgsPack $ ArgsPack argsSupers odEmpty
        else do
          !argsSupers <- sequence $ supersOf <$> args
          !kwargsSupers <- odMapSTM supersOf kwargs
          exitEdh ets exit (EdhArgsPack $ ArgsPack argsSupers kwargsSupers)
  where
    !ctx = edh'context ets
    !scope = contextScope ctx

    supersOf :: EdhValue -> STM EdhValue
    supersOf !v = case v of
      EdhObject !o ->
        {- HLINT ignore "Redundant <$>" -}
        map EdhObject <$> readTVar (edh'obj'supers o) >>= \ !supers ->
          return $ EdhArgsPack $ ArgsPack supers odEmpty
      _ -> return edhNone

-- | utility sandbox(origObj) - transform a vanilla object into a sandbox object
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
--
-- in case the original object is a `scope` object, a shadow copy of the
-- original scope object is returned, which is made a sandbox scope object
sandboxProc :: "origObj" !: Object -> EdhHostProc
sandboxProc (mandatoryArg -> !origObj) !exit !ets =
  case edh'obj'store origObj of
    HostStore !hsd -> case fromDynamic hsd of
      Just (scope :: Scope) -> mkScopeSandbox ets scope $ \ !sbScope ->
        exitEdh ets exit $
          EdhObject $
            origObj
              { edh'obj'store = HostStore $ toDyn sbScope
              }
      Nothing -> goObj
    _ -> goObj
  where
    !ctx = edh'context ets
    goObj = mkObjSandbox ets origObj $ \ !sbScope -> case objClassName origObj of
      "_" -> throwEdh ets UsageError "anonymous sandbox is not reasonable"
      !sbName -> do
        let !sbVal = EdhObject $ edh'scope'this sbScope
        unless (edh'ctx'pure ctx) $
          iopdInsert
            (AttrByName sbName)
            sbVal
            (edh'scope'entity $ contextScope ctx)
        exitEdh ets exit sbVal

-- | utility makeOp(lhExpr, opSym, rhExpr)
makeOpProc :: [EdhValue] -> EdhHostProc
makeOpProc !args !exit = case args of
  [EdhExpr _ !lhe _, EdhString !op, EdhExpr _ !rhe _] -> \ !ets -> do
    !xu <- unsafeIOToSTM newUnique
    exitEdh ets exit $
      EdhExpr
        xu
        (InfixExpr op (ExprSrc lhe noSrcRange) (ExprSrc rhe noSrcRange))
        ""
  _ ->
    throwEdhTx EvalError $ "invalid arguments to makeOp: " <> T.pack (show args)

-- | utility parseEdh(srcCode, srcName='<edh>', lineNo=1)
parseEdhProc ::
  "srcCode" !: Text -> "srcName" ?: Text -> "lineNo" ?: Int -> EdhHostProc
parseEdhProc (mandatoryArg -> !srcCode) (defaultArg "<edh>" -> !srcName) (defaultArg 1 -> !lineNo) !exit !ets =
  parseEdh' world srcName lineNo srcCode >>= \case
    Left !err -> do
      let !msg = T.pack $ errorBundlePretty err
          !edhWrapException = edh'exception'wrapper world
          !edhErr = EdhError ParseError msg (toDyn nil) $ getEdhErrCtx 0 ets
      edhWrapException (toException edhErr)
        >>= \ !exo -> edhThrow ets (EdhObject exo)
    Right (!stmts, _docCmt) -> do
      !u <- unsafeIOToSTM newUnique
      exitEdh ets exit $ EdhExpr u (BlockExpr stmts) srcCode
  where
    world = edh'prog'world $ edh'thread'prog ets
