
module Language.Edh.Details.Evaluate where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Exception
import           Control.Monad.State.Strict
import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Unique
import           Data.Maybe
import           Data.Either
import qualified Data.ByteString               as B
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Text.Encoding
import           Data.Text.Encoding.Error
import qualified Data.HashMap.Strict           as Map
import           Data.List.NonEmpty             ( NonEmpty(..)
                                                , (<|)
                                                )
import qualified Data.List.NonEmpty            as NE
import           Data.Dynamic

import           Text.Megaparsec

import           Data.Lossless.Decimal         as D

import           Language.Edh.Control
import           Language.Edh.Parser
import           Language.Edh.Event

import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.PkgMan
import           Language.Edh.Details.Utils



-- TODO rm this after refactor done
contEdhSTM :: STM () -> EdhProc
contEdhSTM = const


-- todo this should really be in `CoreLang.hs`, but there has no access to 
--      'throwEdh' without cyclic imports, maybe some day we shall try
--      `.hs-boot` files
-- | resolve an attribute addressor, either alphanumeric named or symbolic
resolveEdhAttrAddr
  :: EdhThreadState -> AttrAddressor -> (AttrKey -> STM ()) -> STM ()
resolveEdhAttrAddr _ (NamedAttr !attrName) !exit = exit (AttrByName attrName)
resolveEdhAttrAddr !ets (SymbolicAttr !symName) !exit =
  let scope = contextScope $ edh'context ets
  in  resolveEdhCtxAttr ets scope (AttrByName symName) >>= \case
        Just (!val, _) -> case val of
          (EdhSymbol !symVal ) -> exit (AttrBySym symVal)
          (EdhString !nameVal) -> exit (AttrByName nameVal)
          _ ->
            throwEdh ets EvalError
              $  "Not a symbol/string as "
              <> symName
              <> ", it is a "
              <> T.pack (edhTypeNameOf val)
              <> ": "
              <> T.pack (show val)
        Nothing ->
          throwEdh ets EvalError
            $  "No symbol/string named "
            <> T.pack (show symName)
            <> " available"
{-# INLINE resolveEdhAttrAddr #-}


throwEdhProc :: EdhErrorTag -> Text -> EdhProc
throwEdhProc !et !msg !ets = throwEdh ets et msg
-- | Throw a tagged error from Edh
--
-- a bit similar to `return` in Haskell, this doesn't cease the execution
-- of subsequent actions following it, be cautious.
throwEdh :: EdhThreadState -> EdhErrorTag -> Text -> STM ()
throwEdh !ets !et !msg = getEdhErrClass ets et >>= \ec ->
  runEdhProc ets
    $ constructEdhObject ec (ArgsPack [EdhString msg] odEmpty)
    $ \ !exo -> edhThrow ets exo


edhThrowProc :: EdhValue -> EdhProc
edhThrowProc = flip edhThrow
-- | Throw arbitrary value from Edh
--
-- a bit similar to `return` in Haskell, this doesn't cease the execution
-- of subsequent actions following it, be cautious.
edhThrow :: EdhThreadState -> EdhValue -> STM ()
edhThrow !ets !exv = do
  let propagateExc :: EdhValue -> [Scope] -> STM ()
      propagateExc exv' [] = edhErrorUncaught ets exv'
      propagateExc exv' (frame : stack) =
        runEdhProc ets $ edh'excpt'hndlr frame exv' $ \exv'' ->
          contEdhSTM $ propagateExc exv'' stack
  propagateExc exv $ NE.toList $ edh'ctx'stack $ edh'context ets

edhErrorUncaught :: EdhThreadState -> EdhValue -> STM ()
edhErrorUncaught !ets !exv = case exv of
  EdhObject exo -> do
    esd <- readTVar $ entity'store $ objEntity exo
    case fromDynamic esd :: Maybe SomeException of
      Just !e -> throwSTM e -- TODO replace cc in err if is empty here ?
      Nothing -> edhValueRepr ets exv
        -- TODO support magic method to coerce as exception ?
        $ \msg -> throwSTM $ EdhError EvalError msg $ getEdhCallContext 0 ets
  EdhString !msg -> throwSTM $ EdhError EvalError msg $ getEdhCallContext 0 ets
  _              -> edhValueRepr ets exv
    -- coerce arbitrary value to EdhError
    $ \msg -> throwSTM $ EdhError EvalError msg $ getEdhCallContext 0 ets


edhCatchProc
  :: (EdhExit -> EdhProc) -- ^ tryAct
  -> EdhExit -- ^ normal/recovered exit
  -> (  -- edh'ctx'match of this proc will the thrown value or nil
        EdhExit  -- ^ recover exit
     -> EdhProc  -- ^ rethrow exit
     -> EdhProc
     )
  -> EdhProc
edhCatchProc !tryAct !exit !passOn !etsOuter =
  edhCatch etsOuter (\ !etsTry exit' -> runEdhProc etsTry (tryAct exit')) exit
    $ \_etsThrower !exv recover rethrow -> do
        let !ctxOuter = edh'context etsOuter
            !ctxHndl  = ctxOuter { edh'ctx'match = exv }
            !etsHndl  = etsOuter { edh'context = ctxHndl }
        runEdhProc etsHndl $ passOn recover $ const rethrow
-- | Catch possible throw from the specified try action
edhCatch
  :: EdhThreadState
  -> (EdhThreadState -> EdhExit -> STM ()) -- ^ tryAct
  -> EdhExit -- ^ normal/recovered exit
  -> (  EdhThreadState -- ^ thrower's ets, the task queue is important
     -> EdhValue       -- ^ exception value or nil
     -> EdhExit        -- ^ recover exit
     -> STM ()         -- ^ rethrow exit
     -> STM ()
     )
  -> STM ()
edhCatch !etsOuter !tryAct !exit !passOn = do
  hndlrTh <- unsafeIOToSTM myThreadId
  let
    !ctxOuter   = edh'context etsOuter
    !scopeOuter = contextScope ctxOuter
    !tryScope   = scopeOuter { edh'excpt'hndlr = hndlr }
    !tryCtx =
      ctxOuter { edh'ctx'stack = tryScope :| NE.tail (edh'ctx'stack ctxOuter) }
    !etsTry = etsOuter { edh'context = tryCtx }
    hndlr :: EdhExcptHndlr
    hndlr !exv !rethrow = do
      etsThrower <- ask
      let
        goRecover :: EdhExit
        goRecover !result = ask >>= \ets ->
          -- an exception handler provided another result value to recover
          const $ fromEdhError ets exv $ \ex -> case fromException ex of
            Just ProgramHalt{} -> goRethrow -- never recover from ProgramHalt
            _                  -> do
              -- do recover from the exception
              rcvrTh <- unsafeIOToSTM myThreadId
              if rcvrTh /= hndlrTh
                then -- just skip the action if from a different thread
                     return () -- other than the handler installer
                else runEdhProc etsOuter $ exit result
        goRethrow :: STM ()
        goRethrow =
          runEdhProc etsOuter $ edh'excpt'hndlr scopeOuter exv rethrow
      const $ passOn etsThrower exv goRecover goRethrow
  tryAct etsTry $ \ !tryResult -> const $ do
    -- no exception occurred, go trigger finally block
    rcvrTh <- unsafeIOToSTM myThreadId
    if rcvrTh /= hndlrTh
      then -- just skip the action if from a different thread
           return () -- other than the handler installer
      else
        passOn etsOuter nil (error "bug: recovering from finally block")
          $ exitEdhSTM' etsOuter exit tryResult


-- | Create a tagged Edh error as both an Edh exception value and a host
-- exception value
createEdhError
  :: EdhThreadState
  -> EdhErrorTag
  -> Text
  -> (EdhValue -> SomeException -> STM ())
  -> STM ()
createEdhError !ets !et !msg !exit = getEdhErrClass ets et >>= \ !ec ->
  runEdhProc ets
    $ constructEdhObject ec (ArgsPack [EdhString msg] odEmpty)
    $ \ !exv -> case exv of
        EdhObject !exo -> castObjectStore exo >>= \case
          Just (e :: SomeException, _details :: ArgsPack) -> exit exv e
          Nothing -> castObjectStore exo >>= \case
            Just (e :: SomeException) -> exit exv e
            Nothing -> error "bug: error class gave no host exception"
        _ -> error "bug: error class returned non-object"

-- | Convert an arbitrary Edh error to host exception
fromEdhError
  :: EdhThreadState -> EdhValue -> (SomeException -> STM ()) -> STM ()
fromEdhError !ets !exv !exit = case exv of
  EdhNil ->
    throwSTM
      $ EdhError UsageError "false Edh error to fromEdhError"
      $ getEdhCallContext 0 ets
  EdhObject !exo -> castObjectStore exo >>= \case
    Just (e :: SomeException, _details :: ArgsPack) -> exit e
    Nothing -> castObjectStore exo >>= \case
      Just (e :: SomeException) -> exit e
      Nothing                   -> ioErr
  _ -> ioErr
 where
  ioErr = edhValueRepr ets exv $ \ !exr ->
    exit $ toException $ EdhError EvalError exr $ getEdhCallContext 0 ets

-- | Convert an arbitrary exception to an Edh error
toEdhError :: EdhThreadState -> SomeException -> (EdhValue -> STM ()) -> STM ()
toEdhError !ets !e !exit = toEdhError' ets e (ArgsPack [] odEmpty) exit
-- | Convert an arbitrary exception plus details to an Edh error
toEdhError'
  :: EdhThreadState
  -> SomeException
  -> ArgsPack
  -> (EdhValue -> STM ())
  -> STM ()
toEdhError' !ets !e !details !exit = case fromException e of
  Just (err :: EdhError) -> case err of
    EdhError !et _ _ -> getEdhErrClass ets et >>= withErrCls
    EdhPeerError{} ->
      _getEdhErrClass ets (AttrByName "PeerError") >>= withErrCls
    EdhIOError{} -> _getEdhErrClass ets (AttrByName "IOError") >>= withErrCls
    ProgramHalt{} ->
      _getEdhErrClass ets (AttrByName "ProgramHalt") >>= withErrCls
  Nothing -> _getEdhErrClass ets (AttrByName "IOError") >>= withErrCls
 where
  withErrCls :: Class -> STM ()
  withErrCls !ec = do
    !oid <- unsafeIOToSTM newUnique
    !hsv <- newTVar $ toDyn (e, details)
    !ss  <- newTVar []
    let !exo = Object oid (HostStore hsv) ec ss
    exit $ EdhObject exo

-- | Get Edh class for an error tag
getEdhErrClass :: EdhThreadState -> EdhErrorTag -> STM Class
getEdhErrClass !ets !et = _getEdhErrClass ets eck
 where
  eck = AttrByName $ ecn et
  ecn :: EdhErrorTag -> Text
  ecn = \case -- cross check with 'createEdhWorld' for type safety
    EdhException -> "Exception"
    PackageError -> "PackageError"
    ParseError   -> "ParseError"
    EvalError    -> "EvalError"
    UsageError   -> "UsageError"
_getEdhErrClass :: EdhThreadState -> AttrKey -> STM Class
_getEdhErrClass !ets !eck =
  lookupEntityAttr ets
                   (scopeEntity $ worldScope $ contextWorld $ edh'context ets)
                   eck
    >>= \case
          EdhClass !ec -> return ec
          badVal ->
            throwSTM
              $ EdhError
                  UsageError
                  (  "Edh error class "
                  <> T.pack (show eck)
                  <> " in the world found to be a "
                  <> T.pack (edhTypeNameOf badVal)
                  )
              $ getEdhCallContext 0 ets

createErrorObjSuper :: Text -> Unique -> STM EntityStore
createErrorObjSuper !clsName !clsUniq = do
  let the'lookup'entity'attr _ !k !esd = case fromDynamic esd of
        Just (e :: SomeException, apk :: ArgsPack) -> case k of
          AttrByName "__repr__" -> return $ EdhString $ T.pack $ show e
          AttrByName "details"  -> return $ EdhArgsPack apk
          _                     -> return nil
        Nothing -> case fromDynamic esd of
          Just (apk :: ArgsPack) -> case k of
            AttrByName "__repr__" ->
              return $ EdhString $ clsName <> T.pack (show apk)
            AttrByName "details" -> return $ EdhArgsPack apk
            _                    -> return nil
          Nothing -> case fromDynamic esd of
            Just (e :: SomeException) -> case k of
              AttrByName "__repr__" -> return $ EdhString $ T.pack $ show e
              AttrByName "details" ->
                return $ EdhArgsPack $ ArgsPack [] odEmpty
              _ -> return nil
            Nothing -> case k of
              AttrByName "__repr__" -> return $ EdhString $ clsName <> "()"
              AttrByName "details" ->
                return $ EdhArgsPack $ ArgsPack [] odEmpty
              _ -> return nil
      the'all'entity'attrs _ _ = return []
      the'change'entity'attr !ets _ _ _ =
        throwSTM
          $ EdhError UsageError "Edh error object not changable"
          $ getEdhCallContext 0 ets
      the'update'entity'attrs !ets _ _ =
        throwSTM
          $ EdhError UsageError "Edh error object not changable"
          $ getEdhCallContext 0 ets
  return $ EntityManipulater the'lookup'entity'attr
                             the'all'entity'attrs
                             the'change'entity'attr
                             the'update'entity'attrs




parseEdh :: EdhWorld -> String -> Text -> STM (Either ParserError [StmtSrc])
parseEdh !world !srcName !srcCode = parseEdh' world srcName 1 srcCode
parseEdh'
  :: EdhWorld -> String -> Int -> Text -> STM (Either ParserError [StmtSrc])
parseEdh' !world !srcName !lineNo !srcCode = do
  pd <- takeTMVar wops -- update 'worldOperators' atomically wrt parsing
  let ((_, pr), pd') = runState
        (runParserT'
          parseProgram
          State
            { stateInput       = srcCode
            , stateOffset      = 0
            , statePosState    = PosState
                                   { pstateInput      = srcCode
                                   , pstateOffset     = 0
                                   , pstateSourcePos  = SourcePos
                                                          { sourceName = srcName
                                                          , sourceLine = mkPos
                                                                           lineNo
                                                          , sourceColumn = mkPos 1
                                                          }
                                   , pstateTabWidth   = mkPos 2
                                   , pstateLinePrefix = ""
                                   }
            , stateParseErrors = []
            }
        )
        pd
  case pr of
    -- update operator precedence dict on success of parsing
    Right _ -> putTMVar wops pd'
    -- restore original precedence dict on failure of parsing
    _       -> putTMVar wops pd
  return pr
  where !wops = worldOperators world


evalEdh :: String -> Text -> EdhExit -> EdhProc
evalEdh !srcName = evalEdh' srcName 1
evalEdh' :: String -> Int -> Text -> EdhExit -> EdhProc
evalEdh' !srcName !lineNo !srcCode !exit !ets = do
  let ctx   = edh'context ets
      world = contextWorld ctx
  parseEdh' world srcName lineNo srcCode >>= \case
    Left !err -> getEdhErrClass ets ParseError >>= \ec ->
      runEdhProc ets
        $ createEdhObject
            ec
            (ArgsPack [EdhString $ T.pack $ errorBundlePretty err] odEmpty)
        $ \ !exv -> edhThrowProc exv
    Right !stmts -> runEdhProc ets $ evalBlock stmts exit


deParen :: Expr -> Expr
deParen x = case x of
  ParenExpr x' -> deParen x'
  _            -> x

deApk :: ArgsPack -> ArgsPack
deApk (ArgsPack [EdhArgsPack !apk] !kwargs) | odNull kwargs = apk
deApk apk = apk

evalStmt :: StmtSrc -> EdhExit -> EdhProc
evalStmt ss@(StmtSrc (_sp, !stmt)) !exit !ets =
  runEdhProc ets { edh'context = (edh'context ets) { edh'ctx'stmt = ss } }
    $ evalStmt' stmt
    $ \ !rtn -> exitEdh ets exit rtn

evalCaseBlock :: Expr -> EdhExit -> EdhProc
evalCaseBlock !expr !exit = case expr of
  -- case-of with a block is normal
  BlockExpr stmts' -> evalBlock stmts' exit
  -- single branch case is some special
  _                -> evalExpr expr $ \ !val -> case val of
    -- the only branch did match
    (EdhCaseClose !v) -> exitEdhProc exit $ edhDeCaseClose v
    -- the only branch didn't match
    EdhCaseOther      -> exitEdhProc exit nil
    -- yield should have been handled by 'evalExpr'
    (EdhYield _)      -> throwEdhProc EvalError "bug yield reached block"
    -- ctrl to be propagated outwards, as this is the only stmt, no need to
    -- be specifically written out
    -- EdhFallthrough    -> exitEdhProc exit EdhFallthrough
    -- EdhBreak          -> exitEdhProc exit EdhBreak
    -- EdhContinue       -> exitEdhProc exit EdhContinue
    -- (EdhReturn !v)    -> exitEdhProc exit (EdhReturn v)
    -- other vanilla result, propagate as is
    _                 -> exitEdhProc exit val

evalBlock :: [StmtSrc] -> EdhExit -> EdhProc
evalBlock []    !exit = exitEdhProc exit nil
evalBlock [!ss] !exit = evalStmt ss $ \ !val -> case val of
  -- last branch did match
  (EdhCaseClose !v) -> exitEdhProc exit $ edhDeCaseClose v
  -- yield should have been handled by 'evalExpr'
  (EdhYield     _ ) -> throwEdhProc EvalError "bug yield reached block"
  -- ctrl to be propagated outwards, as this is the last stmt, no need to
  -- be specifically written out
  -- EdhCaseOther      -> exitEdhProc exit EdhCaseOther
  -- EdhFallthrough    -> exitEdhProc exit EdhFallthrough
  -- EdhRethrow        -> exitEdhProc exit EdhRethrow
  -- EdhBreak          -> exitEdhProc exit EdhBreak
  -- EdhContinue       -> exitEdhProc exit EdhContinue
  -- (EdhReturn !v)    -> exitEdhProc exit (EdhReturn v)
  -- other vanilla result, propagate as is
  _                 -> exitEdhProc exit val
evalBlock (ss : rest) !exit = evalStmt ss $ \(OriginalValue !val _ _) ->
  case val of
    -- a branch matched, finish this block
    (EdhCaseClose !v) -> exitEdhProc exit $ edhDeCaseClose v
    -- should continue to next branch (or stmt)
    EdhCaseOther      -> evalBlock rest exit
    -- should fallthrough to next branch (or stmt)
    EdhFallthrough    -> evalBlock rest exit
    -- yield should have been handled by 'evalExpr'
    (EdhYield _)      -> throwEdhProc EvalError "bug yield reached block"
    -- ctrl to interrupt this block, and to be propagated outwards
    EdhRethrow        -> exitEdhProc exit EdhRethrow
    EdhBreak          -> exitEdhProc exit EdhBreak
    EdhContinue       -> exitEdhProc exit EdhContinue
    (EdhReturn !v)    -> exitEdhProc exit (EdhReturn v)
    -- other vanilla result, continue this block
    _                 -> evalBlock rest exit


-- | a left-to-right expr list eval'er, returning a tuple
evalExprs :: [Expr] -> EdhExit -> EdhProc
-- here 'EdhArgsPack' is used for intermediate tag,
-- not intend to return an actual apk value
evalExprs []       !exit = exitEdhProc exit (EdhArgsPack $ ArgsPack [] odEmpty)
evalExprs (x : xs) !exit = evalExpr x $ \(OriginalValue !val _ _) ->
  evalExprs xs $ \(OriginalValue !tv _ _) -> case tv of
    EdhArgsPack (ArgsPack !l _) ->
      exitEdhProc exit (EdhArgsPack $ ArgsPack (edhDeCaseClose val : l) odEmpty)
    _ -> error "bug"


evalStmt' :: Stmt -> EdhExit -> EdhProc
evalStmt' !stmt !exit = do
  !ets <- ask
  let !ctx   = edh'context ets
      !scope = contextScope ctx
      this   = thisObject scope
  case stmt of

    ExprStmt !expr -> evalExpr expr $ \result -> exitEdhProc' exit result

    LetStmt !argsRcvr !argsSndr ->
      -- ensure args sending and receiving happens within a same tx
      -- for atomicity of the let statement
      local (const ets { edh'in'tx = True }) $ packEdhArgs argsSndr $ \ !apk ->
        recvEdhArgs ctx argsRcvr (deApk apk) $ \um -> contEdhSTM $ do
          if not (edh'ctx'eff'defining ctx)
            then -- normal multi-assignment
                 updateEntityAttrs ets (scopeEntity scope) $ odToList um
            else do -- define effectful artifacts by multi-assignment
              let !effd = [ (attrKeyValue k, v) | (k, v) <- odToList um ]
              lookupEntityAttr ets
                               (scopeEntity scope)
                               (AttrByName edhEffectsMagicName)
                >>= \case
                      EdhDict (Dict _ !effDS) -> iopdUpdate effd effDS
                      _                       -> do
                        d <- EdhDict <$> createEdhDict effd
                        changeEntityAttr ets
                                         (scopeEntity scope)
                                         (AttrByName edhEffectsMagicName)
                                         d
          when (edh'ctx'exporting ctx) $ do -- do export what's assigned
            let !impd = [ (attrKeyValue k, v) | (k, v) <- odToList um ]
            lookupEntityAttr ets
                             (objEntity this)
                             (AttrByName edhExportsMagicName)
              >>= \case
                    EdhDict (Dict _ !thisExpDS) -> iopdUpdate impd thisExpDS
                    _                           -> do -- todo warn if of wrong type
                      d <- EdhDict <$> createEdhDict impd
                      changeEntityAttr ets
                                       (objEntity this)
                                       (AttrByName edhExportsMagicName)
                                       d
          exitEdhSTM ets exit nil
          -- let statement evaluates to nil always, with previous tx
          -- state restored

    BreakStmt        -> exitEdhProc exit EdhBreak
    ContinueStmt     -> exitEdhProc exit EdhContinue
    FallthroughStmt  -> exitEdhProc exit EdhFallthrough
    RethrowStmt      -> exitEdhProc exit EdhRethrow

    ReturnStmt !expr -> evalExpr expr $ \(OriginalValue !v2r _ _) ->
      case edhDeCaseClose v2r of
        val@EdhReturn{} -> exitEdhProc exit (EdhReturn val)
          -- actually when a generator procedure checks the result of its `yield`
          -- for the case of early return from the do block, if it wants to
          -- cooperate, double return is the only option
          -- throwEdhProc UsageError "you don't double return"
        !val            -> exitEdhProc exit (EdhReturn val)


    AtoIsoStmt !expr ->
      contEdhSTM
        $ runEdhProc ets { edh'in'tx = True } -- ensure in'tx state
        $ evalExpr expr
        $ \(OriginalValue !val _ _) -> -- restore original tx state
            contEdhSTM $ exitEdhSTM ets exit $ edhDeCaseClose val


    GoStmt !expr -> do
      let doFork :: EdhThreadState -> (Context -> Context) -> EdhProc -> STM ()
          doFork ets' !ctxMod !prog = do
            forkEdh
              ets'
                { edh'context = ctxMod ctx { edh'ctx'match      = true
                                           , edh'ctx'pure        = False
                                           , edh'ctx'exporting   = False
                                           , edh'ctx'eff'defining = False
                                           }
                }
              prog
            exitEdhSTM ets exit nil
      case expr of

        CaseExpr !tgtExpr !branchesExpr ->
          evalExpr tgtExpr $ \(OriginalValue !val _ _) ->
            contEdhSTM
              $ doFork ets
                       (\ctx' -> ctx' { edh'ctx'match = edhDeCaseClose val })
              $ evalCaseBlock branchesExpr endOfEdh

        (CallExpr !procExpr !argsSndr) ->
          contEdhSTM
            $ resolveEdhCallee ets procExpr
            $ \(OriginalValue !callee'val _ !callee'that, scopeMod) ->
                edhMakeCall ets callee'val callee'that argsSndr scopeMod
                  $ \mkCall -> doFork ets id (mkCall endOfEdh)

        (ForExpr !argsRcvr !iterExpr !doExpr) ->
          contEdhSTM
            $ edhForLoop ets argsRcvr iterExpr doExpr (const $ return ())
            $ \runLoop -> doFork ets id (runLoop endOfEdh)

        _ -> contEdhSTM $ doFork ets id $ evalExpr expr endOfEdh


    DeferStmt !expr -> do
      let schedDefered
            :: EdhThreadState -> (Context -> Context) -> EdhProc -> STM ()
          schedDefered !ets' !ctxMod !prog = do
            modifyTVar'
              (edh'defers ets)
              (( ets'
                 { edh'context = ctxMod $ (edh'context ets')
                                   { edh'ctx'match      = true
                                   , edh'ctx'pure        = False
                                   , edh'ctx'exporting   = False
                                   , edh'ctx'eff'defining = False
                                   }
                 }
               , prog
               ) :
              )
            exitEdhSTM ets exit nil
      case expr of

        CaseExpr !tgtExpr !branchesExpr ->
          evalExpr tgtExpr $ \(OriginalValue !val _ _) ->
            contEdhSTM
              $ schedDefered
                  ets
                  (\ctx' -> ctx' { edh'ctx'match = edhDeCaseClose val })
              $ evalCaseBlock branchesExpr endOfEdh

        (CallExpr !procExpr !argsSndr) ->
          contEdhSTM
            $ resolveEdhCallee ets procExpr
            $ \(OriginalValue !callee'val _ !callee'that, scopeMod) ->
                edhMakeCall ets callee'val callee'that argsSndr scopeMod
                  $ \mkCall -> schedDefered ets id (mkCall endOfEdh)

        (ForExpr !argsRcvr !iterExpr !doExpr) ->
          contEdhSTM
            $ edhForLoop ets argsRcvr iterExpr doExpr (const $ return ())
            $ \runLoop -> schedDefered ets id (runLoop endOfEdh)

        _ -> contEdhSTM $ schedDefered ets id $ evalExpr expr endOfEdh


    PerceiveStmt !sinkExpr !bodyExpr ->
      evalExpr sinkExpr $ \(OriginalValue !sinkVal _ _) ->
        case edhUltimate sinkVal of
          (EdhSink sink) -> contEdhSTM $ do
            (perceiverChan, _) <- subscribeEvents sink
            modifyTVar'
              (edh'perceivers ets)
              (( perceiverChan
               , ets
                 { edh'context = ctx { edh'ctx'exporting   = False
                                     , edh'ctx'eff'defining = False
                                     }
                 }
               , bodyExpr
               ) :
              )
            exitEdhSTM ets exit nil
          _ ->
            throwEdhProc EvalError
              $  "Can only perceive from an event sink, not a "
              <> T.pack (edhTypeNameOf sinkVal)
              <> ": "
              <> T.pack (show sinkVal)


    ThrowStmt excExpr -> evalExpr excExpr
      $ \(OriginalValue !exv _ _) -> edhThrowProc $ edhDeCaseClose exv


    WhileStmt !cndExpr !bodyStmt -> do
      let doWhile :: EdhProc
          doWhile = evalExpr cndExpr $ \(OriginalValue !cndVal _ _) ->
            case edhDeCaseClose cndVal of
              (EdhBool True) ->
                evalStmt bodyStmt $ \(OriginalValue !blkVal _ _) ->
                  case edhDeCaseClose blkVal of
                  -- early stop of procedure
                    rtnVal@EdhReturn{} -> exitEdhProc exit rtnVal
                    -- break while loop
                    EdhBreak           -> exitEdhProc exit nil
                    -- continue while loop
                    _                  -> doWhile
              (EdhBool False) -> exitEdhProc exit nil
              EdhNil          -> exitEdhProc exit nil
              _ ->
                throwEdhProc EvalError
                  $  "Invalid condition value for while: "
                  <> T.pack (edhTypeNameOf cndVal)
                  <> ": "
                  <> T.pack (show cndVal)
      doWhile

    ExtendsStmt !superExpr ->
      evalExpr superExpr $ \(OriginalValue !superVal _ _) ->
        case edhDeCaseClose superVal of
          (EdhObject !superObj) -> contEdhSTM $ do
            let
              !magicSpell = AttrByName "<-^"
              noMagic :: EdhProc
              noMagic =
                contEdhSTM $ lookupEdhObjAttr ets superObj magicSpell >>= \case
                  EdhNil    -> exitEdhSTM ets exit nil
                  !magicMth -> withMagicMethod magicMth
              withMagicMethod :: EdhValue -> STM ()
              withMagicMethod magicMth = case magicMth of
                EdhNil              -> exitEdhSTM ets exit nil
                EdhMethod !mth'proc -> do
                  scopeObj <- mkScopeWrapper ctx $ objectScope ctx this
                  runEdhProc ets
                    $ callEdhMethod this
                                    mth'proc
                                    (ArgsPack [EdhObject scopeObj] odEmpty)
                                    id
                    $ \_ -> contEdhSTM $ exitEdhSTM ets exit nil
                _ ->
                  throwEdh ets EvalError
                    $  "Invalid magic (<-^) method type: "
                    <> T.pack (edhTypeNameOf magicMth)
            modifyTVar' (objSupers this) (superObj :)
            runEdhProc ets
              $ getEdhAttrWSM edhMetaMagicSpell superObj magicSpell noMagic
              $ \(OriginalValue !magicMth _ _) ->
                  contEdhSTM $ withMagicMethod magicMth
          _ ->
            throwEdhProc EvalError
              $  "Can only extends an object, not "
              <> T.pack (edhTypeNameOf superVal)
              <> ": "
              <> T.pack (show superVal)

    EffectStmt !effs ->
      local
          (const ets
            { edh'context = (edh'context ets) { edh'ctx'eff'defining = True }
            }
          )
        $ evalExpr effs
        $ \rtn -> local (const ets) $ exitEdhProc' exit rtn

    VoidStmt -> exitEdhProc exit nil

    -- _ -> throwEdhProc EvalError $ "Eval not yet impl for: " <> T.pack (show stmt)


importInto :: Entity -> ArgsReceiver -> Expr -> EdhExit -> EdhProc
importInto !tgtEnt !argsRcvr !srcExpr !exit = case srcExpr of
  LitExpr (StringLiteral !importSpec) ->
    -- import from specified path
    importEdhModule' tgtEnt argsRcvr importSpec exit
  _ -> evalExpr srcExpr $ \(OriginalValue !srcVal _ _) ->
    case edhDeCaseClose srcVal of
      EdhString !importSpec ->
        -- import from dynamic path
        importEdhModule' tgtEnt argsRcvr importSpec exit
      EdhObject !fromObj ->
        -- import from an object
        importFromObject tgtEnt argsRcvr fromObj exit
      EdhArgsPack !fromApk ->
        -- import from an argument pack
        importFromApk tgtEnt argsRcvr fromApk exit
      _ ->
        -- todo support more sources of import ?
        throwEdhProc EvalError
          $  "Don't know how to import from a "
          <> T.pack (edhTypeNameOf srcVal)
          <> ": "
          <> T.pack (show srcVal)


importFromApk :: Entity -> ArgsReceiver -> ArgsPack -> EdhExit -> EdhProc
importFromApk !tgtEnt !argsRcvr !fromApk !exit = do
  ets <- ask
  let !ctx = edh'context ets
  recvEdhArgs ctx argsRcvr fromApk $ \em -> contEdhSTM $ do
    if not (edh'ctx'eff'defining ctx)
      then -- normal import
           updateEntityAttrs ets tgtEnt $ odToList em
      else do -- importing effects
        let !effd = [ (attrKeyValue k, v) | (k, v) <- odToList em ]
        lookupEntityAttr ets tgtEnt (AttrByName edhEffectsMagicName) >>= \case
          EdhDict (Dict _ !effDS) -> iopdUpdate effd effDS
          _                       -> do -- todo warn if of wrong type
            d <- EdhDict <$> createEdhDict effd
            changeEntityAttr ets tgtEnt (AttrByName edhEffectsMagicName) d
    when (edh'ctx'exporting ctx) $ do -- do export what's imported
      let !impd = [ (attrKeyValue k, v) | (k, v) <- odToList em ]
      lookupEntityAttr ets tgtEnt (AttrByName edhExportsMagicName) >>= \case
        EdhDict (Dict _ !thisExpDS) -> iopdUpdate impd thisExpDS
        _                           -> do -- todo warn if of wrong type
          d <- EdhDict <$> createEdhDict impd
          changeEntityAttr ets tgtEnt (AttrByName edhExportsMagicName) d
    exitEdhSTM ets exit $ EdhArgsPack fromApk

edhExportsMagicName :: Text
edhExportsMagicName = "__exports__"

importFromObject :: Entity -> ArgsReceiver -> Object -> EdhExit -> EdhProc
importFromObject !tgtEnt !argsRcvr !fromObj !exit = do
  ets <- ask
  let withExps :: [(AttrKey, EdhValue)] -> STM ()
      withExps !exps =
        runEdhProc ets
          $ importFromApk tgtEnt argsRcvr (ArgsPack [] $ odFromList exps)
          $ \_ -> exitEdhProc exit $ EdhObject fromObj
  contEdhSTM
    $ lookupEntityAttr ets (objEntity fromObj) (AttrByName edhExportsMagicName)
    >>= \case
          EdhNil -> -- nothing exported at all
            withExps []
          EdhDict (Dict _ !fromExpDS) -> iopdToList fromExpDS >>= \ !expl ->
            withExps $ catMaybes
              [ case k of
                  EdhString !expKey -> Just (AttrByName expKey, v)
                  EdhSymbol !expSym -> Just (AttrBySym expSym, v)
                  _                 -> Nothing -- todo warn about this
              | (k, v) <- expl
              ]
          badExplVal ->
            throwEdh ets UsageError $ "bad __exports__ type: " <> T.pack
              (edhTypeNameOf badExplVal)

importEdhModule' :: Entity -> ArgsReceiver -> Text -> EdhExit -> EdhProc
importEdhModule' !tgtEnt !argsRcvr !importSpec !exit =
  importEdhModule importSpec $ \(OriginalValue !moduVal _ _) -> case moduVal of
    EdhObject !modu -> importFromObject tgtEnt argsRcvr modu exit
    _               -> error "bug"

importEdhModule :: Text -> EdhExit -> EdhProc
importEdhModule !impSpec !exit = do
  ets <- ask
  let
    !ctx   = edh'context ets
    !world = contextWorld ctx
    !scope = contextScope ctx
    locateModuInFS :: ((FilePath, FilePath) -> STM ()) -> STM ()
    locateModuInFS !exit' =
      lookupEdhCtxAttr ets scope (AttrByName "__name__") >>= \case
        EdhString !moduName ->
          lookupEdhCtxAttr ets scope (AttrByName "__file__") >>= \case
            EdhString !fromModuPath -> do
              let !importPath = case normalizedSpec of
      -- special case for `import * '.'`, 2 possible use cases:
      --
      --  *) from an entry module (i.e. __main__.edh), to import artifacts
      --     from its respective persistent module
      --
      --  *) from a persistent module, to re-populate the module scope with
      --     its own exports (i.e. the dict __exports__ in its scope), in
      --     case the module scope possibly altered after initialization
                    "." -> T.unpack moduName
                    _   -> T.unpack normalizedSpec
              (nomPath, moduFile) <- unsafeIOToSTM $ locateEdhModule
                (edhPkgPathFrom $ T.unpack fromModuPath)
                importPath
              exit' (nomPath, moduFile)
            _ -> error "bug: no valid `__file__` in context"
        _ -> error "bug: no valid `__name__` in context"
    importFromFS :: STM ()
    importFromFS =
      flip
          catchSTM
          (\(e :: EdhError) -> case e of
            EdhError !et !msg _ -> throwEdh ets et msg
            _                   -> throwSTM e
          )
        $ locateModuInFS
        $ \(nomPath, moduFile) -> do
            let !moduId = T.pack nomPath
            moduMap' <- takeTMVar (worldModules world)
            case Map.lookup moduId moduMap' of
              Just !moduSlot -> do
                -- put back immediately
                putTMVar (worldModules world) moduMap'
                -- blocking wait the target module loaded
                edhPerformSTM ets (readTMVar moduSlot) $ \case
                  -- TODO GHC should be able to detect cyclic imports as 
                  --      deadlock, better to report that more friendly,
                  --      and more importantly, to prevent the crash.
                  EdhNamedValue _ !importError ->
                    -- the first importer failed loading it,
                    -- replicate the error in this thread
                    edhThrowProc importError
                  !modu -> exitEdhProc exit modu
              Nothing -> do -- we are the first importer
                -- allocate an empty slot
                moduSlot <- newEmptyTMVar
                -- put it for global visibility
                putTMVar (worldModules world)
                  $ Map.insert moduId moduSlot moduMap'
                -- try load the module
                runEdhProc ets
                  $ edhCatchProc (loadModule moduSlot moduId moduFile) exit
                  $ \_ !rethrow -> ask >>= \etsPassOn ->
                      case edh'ctx'match $ edh'context etsPassOn of
                        EdhNil      -> rethrow -- no error occurred
                        importError -> contEdhSTM $ do
                          void $ tryPutTMVar moduSlot $ EdhNamedValue
                            "importError"
                            importError
                          -- cleanup on loading error
                          moduMap'' <- takeTMVar (worldModules world)
                          case Map.lookup moduId moduMap'' of
                            Nothing -> putTMVar (worldModules world) moduMap''
                            Just moduSlot' -> if moduSlot' == moduSlot
                              then putTMVar (worldModules world)
                                $ Map.delete moduId moduMap''
                              else putTMVar (worldModules world) moduMap''
                          runEdhProc etsPassOn rethrow
  if edh'in'tx ets
    then throwEdhProc UsageError "You don't import from within a transaction"
    else contEdhSTM $ do
      moduMap <- readTMVar (worldModules world)
      case Map.lookup normalizedSpec moduMap of
        -- attempt the import specification as direct module id first
        Just !moduSlot -> readTMVar moduSlot >>= \case
          -- import error has been encountered, propagate the error
          EdhNamedValue _ !importError ->
            runEdhProc ets $ edhThrowProc importError
          -- module already imported, got it as is
          !modu -> exitEdhSTM ets exit modu
        -- resolving to `.edh` source files from local filesystem
        Nothing -> importFromFS
 where
  normalizedSpec = normalizeImpSpec impSpec
  normalizeImpSpec :: Text -> Text
  normalizeImpSpec = withoutLeadingSlash . withoutTrailingSlash
  withoutLeadingSlash spec = fromMaybe spec $ T.stripPrefix "/" spec
  withoutTrailingSlash spec = fromMaybe spec $ T.stripSuffix "/" spec

loadModule :: TMVar EdhValue -> ModuleId -> FilePath -> EdhExit -> EdhProc
loadModule !moduSlot !moduId !moduFile !exit = ask >>= \etsImporter ->
  if edh'in'tx etsImporter
    then throwEdhProc UsageError
                      "You don't load a module from within a transaction"
    else contEdhSTM $ do
      let !importerCtx = edh'context etsImporter
          !world       = contextWorld importerCtx
      fileContent <-
        unsafeIOToSTM
        $   streamDecodeUtf8With lenientDecode
        <$> B.readFile moduFile
      case fileContent of
        Some !moduSource _ _ -> do
          modu <- createEdhModule' world moduId moduFile
          let !loadScope = objectScope importerCtx modu
              !loadCtx   = importerCtx
                { edh'ctx'stack      = loadScope <| edh'ctx'stack importerCtx
                , edh'ctx'exporting   = False
                , edh'ctx'eff'defining = False
                }
              !etsLoad = etsImporter { edh'context = loadCtx }
          runEdhProc etsLoad $ evalEdh moduFile moduSource $ \_ ->
            contEdhSTM $ do
              -- arm the successfully loaded module
              void $ tryPutTMVar moduSlot $ EdhObject modu
              -- switch back to module importer's scope and continue
              exitEdhSTM etsImporter exit $ EdhObject modu

createEdhModule' :: EdhWorld -> ModuleId -> String -> STM Object
createEdhModule' !world !moduId !srcName = do
  -- prepare the module meta data
  !moduEntity <- createHashEntity =<< iopdFromList
    [ (AttrByName "__name__", EdhString moduId)
    , (AttrByName "__file__", EdhString $ T.pack srcName)
    , (AttrByName "__repr__", EdhString $ "module:" <> moduId)
    ]
  !moduSupers    <- newTVar []
  !moduClassUniq <- unsafeIOToSTM newUnique
  return Object
    { objEntity = moduEntity
    , objClass  = ProcDefi
      { procedure'uniq = moduClassUniq
      , procedure'name = AttrByName $ "module:" <> moduId
      , procedure'lexi = Just $ worldScope world
      , procedure'decl = ProcDecl
                           { procedure'addr = NamedAttr $ "module:" <> moduId
                           , procedure'args = PackReceiver []
                           , procedure'body = Left $ StmtSrc
                                                ( SourcePos
                                                  { sourceName   = srcName
                                                  , sourceLine   = mkPos 1
                                                  , sourceColumn = mkPos 1
                                                  }
                                                , VoidStmt
                                                )
                           }
      }
    , objSupers = moduSupers
    }

moduleContext :: EdhWorld -> Object -> Context
moduleContext !world !modu = worldCtx
  { edh'ctx'stack      = objectScope worldCtx modu <| edh'ctx'stack worldCtx
  , edh'ctx'exporting   = False
  , edh'ctx'eff'defining = False
  }
  where !worldCtx = worldContext world


intplExpr :: EdhThreadState -> Expr -> (Expr -> STM ()) -> STM ()
intplExpr !ets !x !exit = case x of
  IntplExpr !x' -> runEdhProc ets $ evalExpr x' $ \(OriginalValue !val _ _) ->
    contEdhSTM $ exit $ IntplSubs val
  PrefixExpr !pref !x' -> intplExpr ets x' $ \x'' -> exit $ PrefixExpr pref x''
  IfExpr !cond !cons !alt -> intplExpr ets cond $ \cond' ->
    intplExpr ets cons $ \cons' -> case alt of
      Nothing -> exit $ IfExpr cond' cons' Nothing
      Just !altx ->
        intplExpr ets altx $ \altx' -> exit $ IfExpr cond' cons' $ Just altx'
  CaseExpr !tgt !branches -> intplExpr ets tgt $ \tgt' ->
    intplExpr ets branches $ \branches' -> exit $ CaseExpr tgt' branches'
  DictExpr !entries -> seqcontSTM (intplDictEntry ets <$> entries)
    $ \entries' -> exit $ DictExpr entries'
  ListExpr !es ->
    seqcontSTM (intplExpr ets <$> es) $ \es' -> exit $ ListExpr es'
  ArgsPackExpr !argSenders -> seqcontSTM (intplArgSender ets <$> argSenders)
    $ \argSenders' -> exit $ ArgsPackExpr argSenders'
  ParenExpr !x' -> intplExpr ets x' $ \x'' -> exit $ ParenExpr x''
  BlockExpr !ss ->
    seqcontSTM (intplStmtSrc ets <$> ss) $ \ss' -> exit $ BlockExpr ss'
  YieldExpr !x'             -> intplExpr ets x' $ \x'' -> exit $ YieldExpr x''
  ForExpr !rcvs !fromX !doX -> intplExpr ets fromX
    $ \fromX' -> intplExpr ets doX $ \doX' -> exit $ ForExpr rcvs fromX' doX'
  AttrExpr !addr -> intplAttrAddr ets addr $ \addr' -> exit $ AttrExpr addr'
  IndexExpr !v !t ->
    intplExpr ets v $ \v' -> intplExpr ets t $ \t' -> exit $ IndexExpr v' t'
  CallExpr !v !args -> intplExpr ets v $ \v' ->
    seqcontSTM (intplArgSndr ets <$> args) $ \args' -> exit $ CallExpr v' args'
  InfixExpr !op !lhe !rhe -> intplExpr ets lhe
    $ \lhe' -> intplExpr ets rhe $ \rhe' -> exit $ InfixExpr op lhe' rhe'
  ImportExpr !rcvrs !xFrom !maybeInto -> intplArgsRcvr ets rcvrs $ \rcvrs' ->
    intplExpr ets xFrom $ \xFrom' -> case maybeInto of
      Nothing     -> exit $ ImportExpr rcvrs' xFrom' Nothing
      Just !oInto -> intplExpr ets oInto
        $ \oInto' -> exit $ ImportExpr rcvrs' xFrom' $ Just oInto'
  _ -> exit x

intplDictEntry
  :: EdhThreadState
  -> (DictKeyExpr, Expr)
  -> ((DictKeyExpr, Expr) -> STM ())
  -> STM ()
intplDictEntry !ets (k@LitDictKey{}, !x) !exit =
  intplExpr ets x $ \x' -> exit (k, x')
intplDictEntry !ets (AddrDictKey !k, !x) !exit = intplAttrAddr ets k
  $ \k' -> intplExpr ets x $ \x' -> exit (AddrDictKey k', x')
intplDictEntry !ets (ExprDictKey !k, !x) !exit =
  intplExpr ets k $ \k' -> intplExpr ets x $ \x' -> exit (ExprDictKey k', x')

intplArgSender :: EdhThreadState -> ArgSender -> (ArgSender -> STM ()) -> STM ()
intplArgSender !ets (UnpackPosArgs !x) !exit =
  intplExpr ets x $ \x' -> exit $ UnpackPosArgs x'
intplArgSender !ets (UnpackKwArgs !x) !exit =
  intplExpr ets x $ \x' -> exit $ UnpackKwArgs x'
intplArgSender !ets (UnpackPkArgs !x) !exit =
  intplExpr ets x $ \x' -> exit $ UnpackPkArgs x'
intplArgSender !ets (SendPosArg !x) !exit =
  intplExpr ets x $ \x' -> exit $ SendPosArg x'
intplArgSender !ets (SendKwArg !addr !x) !exit =
  intplExpr ets x $ \x' -> exit $ SendKwArg addr x'

intplAttrAddr :: EdhThreadState -> AttrAddr -> (AttrAddr -> STM ()) -> STM ()
intplAttrAddr !ets !addr !exit = case addr of
  IndirectRef !x' !a -> intplExpr ets x' $ \x'' -> exit $ IndirectRef x'' a
  _                  -> exit addr

intplArgsRcvr
  :: EdhThreadState -> ArgsReceiver -> (ArgsReceiver -> STM ()) -> STM ()
intplArgsRcvr !ets !a !exit = case a of
  PackReceiver !rcvrs ->
    seqcontSTM (intplArgRcvr <$> rcvrs) $ \rcvrs' -> exit $ PackReceiver rcvrs'
  SingleReceiver !rcvr ->
    intplArgRcvr rcvr $ \rcvr' -> exit $ SingleReceiver rcvr'
  WildReceiver -> exit WildReceiver
 where
  intplArgRcvr :: ArgReceiver -> (ArgReceiver -> STM ()) -> STM ()
  intplArgRcvr !a' !exit' = case a' of
    RecvArg !attrAddr !maybeAddr !maybeDefault -> case maybeAddr of
      Nothing -> case maybeDefault of
        Nothing -> exit' $ RecvArg attrAddr Nothing Nothing
        Just !x ->
          intplExpr ets x $ \x' -> exit' $ RecvArg attrAddr Nothing $ Just x'
      Just !addr -> intplAttrAddr ets addr $ \addr' -> case maybeDefault of
        Nothing -> exit' $ RecvArg attrAddr (Just addr') Nothing
        Just !x -> intplExpr ets x
          $ \x' -> exit' $ RecvArg attrAddr (Just addr') $ Just x'

    _ -> exit' a'

intplArgSndr :: EdhThreadState -> ArgSender -> (ArgSender -> STM ()) -> STM ()
intplArgSndr !ets !a !exit' = case a of
  UnpackPosArgs !v -> intplExpr ets v $ \v' -> exit' $ UnpackPosArgs v'
  UnpackKwArgs  !v -> intplExpr ets v $ \v' -> exit' $ UnpackKwArgs v'
  UnpackPkArgs  !v -> intplExpr ets v $ \v' -> exit' $ UnpackPkArgs v'
  SendPosArg    !v -> intplExpr ets v $ \v' -> exit' $ SendPosArg v'
  SendKwArg !n !v  -> intplExpr ets v $ \v' -> exit' $ SendKwArg n v'

intplStmtSrc :: EdhThreadState -> StmtSrc -> (StmtSrc -> STM ()) -> STM ()
intplStmtSrc !ets (StmtSrc (!sp, !stmt)) !exit' =
  intplStmt ets stmt $ \stmt' -> exit' $ StmtSrc (sp, stmt')

intplStmt :: EdhThreadState -> Stmt -> (Stmt -> STM ()) -> STM ()
intplStmt !ets !stmt !exit = case stmt of
  AtoIsoStmt !x         -> intplExpr ets x $ \x' -> exit $ AtoIsoStmt x'
  GoStmt     !x         -> intplExpr ets x $ \x' -> exit $ GoStmt x'
  DeferStmt  !x         -> intplExpr ets x $ \x' -> exit $ DeferStmt x'
  LetStmt !rcvrs !sndrs -> intplArgsRcvr ets rcvrs $ \rcvrs' ->
    seqcontSTM (intplArgSndr ets <$> sndrs)
      $ \sndrs' -> exit $ LetStmt rcvrs' sndrs'
  ExtendsStmt !x           -> intplExpr ets x $ \x' -> exit $ ExtendsStmt x'
  PerceiveStmt !sink !body -> intplExpr ets sink
    $ \sink' -> intplExpr ets body $ \body' -> exit $ PerceiveStmt sink' body'
  WhileStmt !cond !act -> intplExpr ets cond
    $ \cond' -> intplStmtSrc ets act $ \act' -> exit $ WhileStmt cond' act'
  ThrowStmt  !x -> intplExpr ets x $ \x' -> exit $ ThrowStmt x'
  ReturnStmt !x -> intplExpr ets x $ \x' -> exit $ ReturnStmt x'
  ExprStmt   !x -> intplExpr ets x $ \x' -> exit $ ExprStmt x'
  _             -> exit stmt


evalLiteral :: Literal -> STM EdhValue
evalLiteral = \case
  DecLiteral    !v -> return (EdhDecimal v)
  StringLiteral !v -> return (EdhString v)
  BoolLiteral   !v -> return (EdhBool v)
  NilLiteral       -> return nil
  TypeLiteral !v   -> return (EdhType v)
  SinkCtor         -> EdhSink <$> newEventSink

evalAttrAddr :: AttrAddr -> EdhExit -> EdhProc
evalAttrAddr !addr !exit = do
  !ets <- ask
  let !ctx   = edh'context ets
      !scope = contextScope ctx
  case addr of
    ThisRef          -> exitEdhProc exit (EdhObject $ thisObject scope)
    ThatRef          -> exitEdhProc exit (EdhObject $ thatObject scope)
    SuperRef -> throwEdhProc UsageError "Can not address a single super alone"
    DirectRef !addr' -> contEdhSTM $ resolveEdhAttrAddr ets addr' $ \key ->
      lookupEdhCtxAttr ets scope key >>= \case
        EdhNil ->
          throwEdh ets EvalError $ "Not in scope: " <> T.pack (show addr')
        !val -> exitEdhSTM ets exit val
    IndirectRef !tgtExpr !addr' ->
      contEdhSTM $ resolveEdhAttrAddr ets addr' $ \key ->
        runEdhProc ets $ getEdhAttr
          tgtExpr
          key
          (\tgtVal ->
            throwEdhProc EvalError
              $  "No such attribute "
              <> T.pack (show key)
              <> " from a "
              <> T.pack (edhTypeNameOf tgtVal)
              <> ": "
              <> T.pack (show tgtVal)
          )
          exit

evalDictLit
  :: [(DictKeyExpr, Expr)] -> [(EdhValue, EdhValue)] -> EdhExit -> EdhProc
evalDictLit [] !dsl !exit = ask >>= \ets -> contEdhSTM $ do
  u   <- unsafeIOToSTM newUnique
  -- entry order in DictExpr is reversed as from source, we reversed it again
  -- here, so dsl now is the same order as in source code
  dsv <- iopdFromList dsl
  exitEdhSTM ets exit $ EdhDict $ Dict u dsv
evalDictLit ((k, v) : entries) !dsl !exit = case k of
  LitDictKey !lit -> evalExpr v $ \(OriginalValue vVal _ _) -> do
    ets <- ask
    contEdhSTM $ evalLiteral lit >>= \kVal ->
      runEdhProc ets $ evalDictLit entries ((kVal, vVal) : dsl) exit
  AddrDictKey !addr -> evalAttrAddr addr $ \(OriginalValue !kVal _ _) ->
    evalExpr v $ \(OriginalValue !vVal _ _) ->
      evalDictLit entries ((kVal, vVal) : dsl) exit
  ExprDictKey !kExpr -> evalExpr kExpr $ \(OriginalValue !kVal _ _) ->
    evalExpr v $ \(OriginalValue !vVal _ _) ->
      evalDictLit entries ((kVal, vVal) : dsl) exit


evalExpr :: Expr -> EdhExit -> EdhProc
evalExpr !expr !exit = do
  !ets <- ask
  let
    !ctx                   = edh'context ets
    !world                 = contextWorld ctx
    !genr'caller           = generatorCaller ctx
    (StmtSrc (!srcPos, _)) = edh'ctx'stmt ctx
    !scope                 = contextScope ctx
    this                   = thisObject scope
    chkExport :: AttrKey -> EdhValue -> STM ()
    chkExport !key !val =
      when (edh'ctx'exporting ctx)
        $ lookupEntityAttr ets (objEntity this) (AttrByName edhExportsMagicName)
        >>= \case
              EdhDict (Dict _ !thisExpDS) ->
                iopdInsert (attrKeyValue key) val thisExpDS
              _ -> do
                d <- EdhDict <$> createEdhDict [(attrKeyValue key, val)]
                changeEntityAttr ets
                                 (objEntity this)
                                 (AttrByName edhExportsMagicName)
                                 d
    defEffect :: AttrKey -> EdhValue -> STM ()
    defEffect !key !val =
      lookupEntityAttr ets (scopeEntity scope) (AttrByName edhEffectsMagicName)
        >>= \case
              EdhDict (Dict _ !effDS) ->
                iopdInsert (attrKeyValue key) val effDS
              _ -> do
                d <- EdhDict <$> createEdhDict [(attrKeyValue key, val)]
                changeEntityAttr ets
                                 (scopeEntity scope)
                                 (AttrByName edhEffectsMagicName)
                                 d
  case expr of

    IntplSubs !val -> exitEdhProc exit val
    IntplExpr _ ->
      throwEdhProc UsageError "Interpolating out side of expr range."
    ExprWithSrc !x !sss -> contEdhSTM $ intplExpr ets x $ \x' -> do
      let intplSrc :: SourceSeg -> (Text -> STM ()) -> STM ()
          intplSrc !ss !exit' = case ss of
            SrcSeg !s -> exit' s
            IntplSeg !sx ->
              runEdhProc ets $ evalExpr sx $ \(OriginalValue !val _ _) ->
                edhValueReprProc (edhDeCaseClose val)
                  $ \(OriginalValue !rv _ _) -> case rv of
                      EdhString !rs -> contEdhSTM $ exit' rs
                      _ -> error "bug: edhValueReprProc returned non-string"
      seqcontSTM (intplSrc <$> sss) $ \ssl -> do
        u <- unsafeIOToSTM newUnique
        exitEdhSTM ets exit $ EdhExpr u x' $ T.concat ssl

    LitExpr !lit -> contEdhSTM $ evalLiteral lit >>= exitEdhSTM ets exit

    PrefixExpr !prefix !expr' -> case prefix of
      PrefixPlus  -> evalExpr expr' exit
      PrefixMinus -> evalExpr expr' $ \(OriginalValue !val _ _) ->
        case edhDeCaseClose val of
          (EdhDecimal !v) -> exitEdhProc exit (EdhDecimal (-v))
          !v ->
            throwEdhProc EvalError
              $  "Can not negate a "
              <> T.pack (edhTypeNameOf v)
              <> ": "
              <> T.pack (show v)
              <> " ❌"
      Not -> evalExpr expr' $ \(OriginalValue !val _ _) ->
        case edhDeCaseClose val of
          (EdhBool v) -> exitEdhProc exit (EdhBool $ not v)
          !v ->
            throwEdhProc EvalError
              $  "Expect bool but got a "
              <> T.pack (edhTypeNameOf v)
              <> ": "
              <> T.pack (show v)
              <> " ❌"
      Guard -> contEdhSTM $ do
        (consoleLogger $ worldConsole world)
          30
          (Just $ sourcePosPretty srcPos)
          (ArgsPack [EdhString "Standalone guard treated as plain value."]
                    odEmpty
          )
        runEdhProc ets $ evalExpr expr' exit

    IfExpr !cond !cseq !alt -> evalExpr cond $ \(OriginalValue !val _ _) ->
      case edhDeCaseClose val of
        (EdhBool True ) -> evalExpr cseq exit
        (EdhBool False) -> case alt of
          Just elseClause -> evalExpr elseClause exit
          _               -> exitEdhProc exit nil
        !v ->
          -- we are so strongly typed
          throwEdhProc EvalError
            $  "Expecting a boolean value but got a "
            <> T.pack (edhTypeNameOf v)
            <> ": "
            <> T.pack (show v)
            <> " ❌"

    DictExpr !entries -> -- make sure dict k:v pairs are evaluated in same tx
      local (\s -> s { edh'in'tx = True })
        $ evalDictLit entries []
          -- restore tx state
        $ \(OriginalValue !dv _ _) -> local (const ets) $ exitEdhProc exit dv

    ListExpr !xs -> -- make sure list values are evaluated in same tx
      local (\s -> s { edh'in'tx = True })
        $ evalExprs xs
        $ \(OriginalValue !tv _ _) -> case tv of
            EdhArgsPack (ArgsPack !l _) -> contEdhSTM $ do
              ll <- newTVar l
              u  <- unsafeIOToSTM newUnique
              -- restore tx state
              exitEdhSTM ets exit (EdhList $ List u ll)
            _ -> error "bug"

    ArgsPackExpr !argSenders ->
      -- make sure packed values are evaluated in same tx
      local (\s -> s { edh'in'tx = True }) $ packEdhArgs argSenders $ \apk ->
        exitEdhProc exit $ EdhArgsPack apk

    ParenExpr !x     -> evalExpr x exit

    BlockExpr !stmts -> evalBlock stmts $ \(OriginalValue !blkResult _ _) ->
      -- a branch match won't escape out of a block, so adjacent blocks always
      -- execute sequentially
      exitEdhProc exit $ edhDeCaseClose blkResult

    CaseExpr !tgtExpr !branchesExpr ->
      evalExpr tgtExpr $ \(OriginalValue !tgtVal _ _) ->
        local
            (const ets
              { edh'context = ctx { edh'ctx'match = edhDeCaseClose tgtVal }
              }
            )
          $ evalCaseBlock branchesExpr
          -- restore program state after block done
          $ \(OriginalValue !blkResult _ _) ->
              local (const ets) $ exitEdhProc exit blkResult


    -- yield stmt evals to the value of caller's `do` expression
    YieldExpr !yieldExpr ->
      evalExpr yieldExpr $ \(OriginalValue !valToYield _ _) ->
        case genr'caller of
          Nothing -> throwEdhProc EvalError "Unexpected yield"
          Just (etsGenrCaller, yieldVal) ->
            contEdhSTM
              $ runEdhProc etsGenrCaller
              $ yieldVal (edhDeCaseClose valToYield)
              $ \case
                  Left (etsThrower, exv) ->
                    edhThrow etsThrower { edh'context = edh'context ets } exv
                  Right !doResult -> case edhDeCaseClose doResult of
                    EdhContinue -> -- for loop should send nil here instead in
                      -- case continue issued from the do block
                      throwEdh ets EvalError "<continue> reached yield"
                    EdhBreak -> -- for loop is breaking, let the generator
                      -- return nil
                      -- the generator can intervene the return, that'll be
                      -- black magic
                      exitEdhSTM ets exit $ EdhReturn EdhNil
                    EdhReturn EdhReturn{} -> -- this must be synthesiszed,
                      -- in case do block issued return, the for loop wrap it as
                      -- double return, so as to let the yield expr in the generator
                      -- propagate the value return, as the result of the for loop
                      -- the generator can intervene the return, that'll be
                      -- black magic
                      exitEdhSTM ets exit doResult
                    EdhReturn{} -> -- for loop should have double-wrapped the
                      -- return, which is handled above, in case its do block
                      -- issued a return
                      throwEdh ets EvalError "<return> reached yield"
                    !val -> exitEdhSTM ets exit val

    ForExpr !argsRcvr !iterExpr !doExpr ->
      contEdhSTM
        $ edhForLoop ets argsRcvr iterExpr doExpr (const $ return ())
        $ \runLoop -> runEdhProc ets (runLoop exit)

    PerformExpr !effAddr ->
      contEdhSTM $ resolveEdhAttrAddr ets effAddr $ \ !effKey ->
        resolveEdhPerform ets effKey $ exitEdhSTM ets exit

    BehaveExpr !effAddr ->
      contEdhSTM $ resolveEdhAttrAddr ets effAddr $ \ !effKey ->
        resolveEdhBehave ets effKey $ exitEdhSTM ets exit

    AttrExpr !addr -> evalAttrAddr addr exit

    IndexExpr !ixExpr !tgtExpr ->
      evalExpr ixExpr $ \(OriginalValue !ixV _ _) ->
        let !ixVal = edhDeCaseClose ixV
        in
          evalExpr tgtExpr $ \(OriginalValue !tgtV _ _) ->
            case edhDeCaseClose tgtV of

              -- indexing a dict
              (EdhDict (Dict _ !d)) ->
                contEdhSTM $ iopdLookup ixVal d >>= \case
                  Nothing  -> exitEdhSTM ets exit nil
                  Just val -> exitEdhSTM ets exit val

              -- indexing an apk
              EdhArgsPack (ArgsPack !args !kwargs) -> case edhUltimate ixVal of
                EdhDecimal !idxNum -> case D.decimalToInteger idxNum of
                  Just !i -> if i < 0 || i >= fromIntegral (length args)
                    then
                      throwEdhProc UsageError
                      $  "apk index out of bounds: "
                      <> T.pack (show i)
                      <> " vs "
                      <> T.pack (show $ length args)
                    else exitEdhProc exit $ args !! fromInteger i
                  Nothing ->
                    throwEdhProc UsageError
                      $  "Invalid numeric index to an apk: "
                      <> T.pack (show idxNum)
                EdhString !attrName -> exitEdhProc exit
                  $ odLookupDefault EdhNil (AttrByName attrName) kwargs
                EdhSymbol !attrSym -> exitEdhProc exit
                  $ odLookupDefault EdhNil (AttrBySym attrSym) kwargs
                !badIdxVal ->
                  throwEdhProc UsageError
                    $  "Invalid index to an apk: "
                    <> T.pack (edhTypeNameOf badIdxVal)

              -- indexing an object, by calling its ([]) method with ixVal as the single arg
              EdhObject !obj ->
                contEdhSTM
                  $   lookupEdhObjAttr ets obj (AttrByName "[]")
                  >>= \case

                        EdhNil ->
                          throwEdh ets EvalError
                            $  "No ([]) method from: "
                            <> T.pack (show obj)

                        EdhMethod !mth'proc -> runEdhProc ets $ callEdhMethod
                          obj
                          mth'proc
                          (ArgsPack [ixVal] odEmpty)
                          id
                          exit

                        !badIndexer ->
                          throwEdh ets EvalError
                            $  "Malformed index method ([]) on "
                            <> T.pack (show obj)
                            <> " - "
                            <> T.pack (edhTypeNameOf badIndexer)
                            <> ": "
                            <> T.pack (show badIndexer)

              tgtVal ->
                throwEdhProc EvalError
                  $  "Don't know how to index "
                  <> T.pack (edhTypeNameOf tgtVal)
                  <> ": "
                  <> T.pack (show tgtVal)
                  <> " with "
                  <> T.pack (edhTypeNameOf ixVal)
                  <> ": "
                  <> T.pack (show ixVal)


    CallExpr !procExpr !argsSndr ->
      contEdhSTM
        $ resolveEdhCallee ets procExpr
        $ \(OriginalValue !callee'val _ !callee'that, scopeMod) ->
            edhMakeCall ets callee'val callee'that argsSndr scopeMod
              $ \mkCall -> runEdhProc ets (mkCall exit)


    InfixExpr !opSym !lhExpr !rhExpr ->
      let
        notApplicable !lhVal !rhVal =
          throwEdh ets EvalError
            $  "Operator ("
            <> opSym
            <> ") not applicable to "
            <> T.pack (edhTypeNameOf $ edhUltimate lhVal)
            <> " and "
            <> T.pack (edhTypeNameOf $ edhUltimate rhVal)
        tryMagicMethod :: EdhValue -> EdhValue -> STM () -> STM ()
        tryMagicMethod !lhVal !rhVal !naExit = case edhUltimate lhVal of
          EdhObject !lhObj ->
            lookupEdhObjAttr ets lhObj (AttrByName opSym) >>= \case
              EdhNil -> case edhUltimate rhVal of
                EdhObject !rhObj ->
                  lookupEdhObjAttr ets rhObj (AttrByName $ opSym <> "@")
                    >>= \case
                          EdhNil              -> naExit
                          EdhMethod !mth'proc -> runEdhProc ets $ callEdhMethod
                            rhObj
                            mth'proc
                            (ArgsPack [lhVal] odEmpty)
                            id
                            exit
                          !badEqMth ->
                            throwEdh ets UsageError
                              $  "Malformed magic method ("
                              <> opSym
                              <> "@) on "
                              <> T.pack (show rhObj)
                              <> " - "
                              <> T.pack (edhTypeNameOf badEqMth)
                              <> ": "
                              <> T.pack (show badEqMth)
                _ -> naExit
              EdhMethod !mth'proc -> runEdhProc ets $ callEdhMethod
                lhObj
                mth'proc
                (ArgsPack [rhVal] odEmpty)
                id
                exit
              !badEqMth ->
                throwEdh ets UsageError
                  $  "Malformed magic method ("
                  <> opSym
                  <> ") on "
                  <> T.pack (show lhObj)
                  <> " - "
                  <> T.pack (edhTypeNameOf badEqMth)
                  <> ": "
                  <> T.pack (show badEqMth)
          _ -> case edhUltimate rhVal of
            EdhObject !rhObj ->
              lookupEdhObjAttr ets rhObj (AttrByName $ opSym <> "@") >>= \case
                EdhNil              -> naExit
                EdhMethod !mth'proc -> runEdhProc ets $ callEdhMethod
                  rhObj
                  mth'proc
                  (ArgsPack [lhVal] odEmpty)
                  id
                  exit
                !badEqMth ->
                  throwEdh ets UsageError
                    $  "Malformed magic method ("
                    <> opSym
                    <> "@) on "
                    <> T.pack (show rhObj)
                    <> " - "
                    <> T.pack (edhTypeNameOf badEqMth)
                    <> ": "
                    <> T.pack (show badEqMth)
            _ -> naExit
      in
        contEdhSTM $ resolveEdhCtxAttr ets scope (AttrByName opSym) >>= \case
          Nothing ->
            runEdhProc ets $ evalExpr lhExpr $ \(OriginalValue lhVal _ _) ->
              evalExpr rhExpr $ \(OriginalValue rhVal _ _) ->
                contEdhSTM $ tryMagicMethod lhVal rhVal $ notApplicable lhVal
                                                                        rhVal
          Just (!opVal, !op'lexi) -> case opVal of

            -- calling an intrinsic operator
            EdhIntrOp _ (IntrinOpDefi _ _ iop'proc) ->
              runEdhProc ets
                $ iop'proc lhExpr rhExpr
                $ \rtn@(OriginalValue !rtnVal _ _) ->
                    case edhDeCaseClose rtnVal of
                      EdhDefault !defResult ->
                        evalExpr lhExpr $ \(OriginalValue lhVal _ _) ->
                          evalExpr rhExpr $ \(OriginalValue rhVal _ _) ->
                            contEdhSTM $ tryMagicMethod lhVal rhVal $ exitEdhSTM
                              ets
                              exit
                              defResult
                      EdhContinue ->
                        evalExpr lhExpr $ \(OriginalValue lhVal _ _) ->
                          evalExpr rhExpr $ \(OriginalValue rhVal _ _) ->
                            contEdhSTM
                              $ tryMagicMethod lhVal rhVal
                              $ notApplicable lhVal rhVal
                      _ -> exitEdhProc' exit rtn

            -- calling an operator procedure
            EdhOprtor _ !op'pred !op'proc ->
              case procedure'args $ procedure'decl op'proc of
                -- 2 pos-args - simple lh/rh value receiving operator
                (PackReceiver [RecvArg{}, RecvArg{}]) ->
                  runEdhProc ets
                    $ evalExpr lhExpr
                    $ \(OriginalValue lhVal _ _) ->
                        evalExpr rhExpr $ \(OriginalValue rhVal _ _) ->
                          callEdhOperator
                              (thatObject op'lexi)
                              op'proc
                              op'pred
                              [edhDeCaseClose lhVal, edhDeCaseClose rhVal]
                            $ \rtn@(OriginalValue !rtnVal _ _) ->
                                case edhDeCaseClose rtnVal of
                                  EdhDefault !defResult ->
                                    contEdhSTM
                                      $ tryMagicMethod lhVal rhVal
                                      $ exitEdhSTM ets exit defResult
                                  EdhContinue ->
                                    contEdhSTM
                                      $ tryMagicMethod lhVal rhVal
                                      $ notApplicable lhVal rhVal
                                  _ -> exitEdhProc' exit rtn

                -- 3 pos-args - caller scope + lh/rh expr receiving operator
                (PackReceiver [RecvArg{}, RecvArg{}, RecvArg{}]) -> do
                  lhu          <- unsafeIOToSTM newUnique
                  rhu          <- unsafeIOToSTM newUnique
                  scopeWrapper <- mkScopeWrapper ctx scope
                  runEdhProc ets
                    $ callEdhOperator
                        (thatObject op'lexi)
                        op'proc
                        op'pred
                        [ EdhObject scopeWrapper
                        , EdhExpr lhu lhExpr ""
                        , EdhExpr rhu rhExpr ""
                        ]
                    $ \rtn@(OriginalValue !rtnVal _ _) ->
                        case edhDeCaseClose rtnVal of
                          EdhDefault !defResult ->
                            evalExpr lhExpr $ \(OriginalValue lhVal _ _) ->
                              evalExpr rhExpr $ \(OriginalValue rhVal _ _) ->
                                contEdhSTM
                                  $ tryMagicMethod lhVal rhVal
                                  $ exitEdhSTM ets exit defResult
                          EdhContinue ->
                            evalExpr lhExpr $ \(OriginalValue lhVal _ _) ->
                              evalExpr rhExpr $ \(OriginalValue rhVal _ _) ->
                                contEdhSTM
                                  $ tryMagicMethod lhVal rhVal
                                  $ notApplicable lhVal rhVal
                          _ -> exitEdhProc' exit rtn

                _ ->
                  throwEdh ets EvalError
                    $  "Invalid operator signature: "
                    <> T.pack (show $ procedure'args $ procedure'decl op'proc)

            _ ->
              throwEdh ets EvalError
                $  "Not callable "
                <> T.pack (edhTypeNameOf opVal)
                <> ": "
                <> T.pack (show opVal)
                <> " expressed with: "
                <> T.pack (show expr)

    NamespaceExpr pd@(ProcDecl !addr _ _) !argsSndr ->
      packEdhArgs argsSndr $ \apk ->
        contEdhSTM $ resolveEdhAttrAddr ets addr $ \name -> do
          u <- unsafeIOToSTM newUnique
          let !cls = ProcDefi { procedure'uniq = u
                              , procedure'name = name
                              , procedure'lexi = Just scope
                              , procedure'decl = pd
                              }
          runEdhProc ets
            $ createEdhObject cls apk
            $ \(OriginalValue !nsv _ _) -> case nsv of
                EdhObject !nso -> contEdhSTM $ do
                  lookupEdhObjAttr ets nso (AttrByName "__repr__") >>= \case
                    EdhNil ->
                      changeEntityAttr ets
                                       (objEntity nso)
                                       (AttrByName "__repr__")
                        $  EdhString
                        $  "namespace:"
                        <> if addr == NamedAttr "_"
                             then "<anonymous>"
                             else T.pack $ show addr
                    _ -> pure ()
                  when (addr /= NamedAttr "_") $ do
                    if edh'ctx'eff'defining ctx
                      then defEffect name nsv
                      else unless (edh'ctx'pure ctx)
                        $ changeEntityAttr ets (scopeEntity scope) name nsv
                    chkExport name nsv
                  exitEdhSTM ets exit nsv
                _ -> error "bug: createEdhObject returned non-object"

    ClassExpr pd@(ProcDecl !addr _ _) ->
      contEdhSTM $ resolveEdhAttrAddr ets addr $ \name -> do
        u <- unsafeIOToSTM newUnique
        let !cls = EdhClass ProcDefi { procedure'uniq = u
                                     , procedure'name = name
                                     , procedure'lexi = Just scope
                                     , procedure'decl = pd
                                     }
        when (addr /= NamedAttr "_") $ do
          if edh'ctx'eff'defining ctx
            then defEffect name cls
            else unless (edh'ctx'pure ctx)
              $ changeEntityAttr ets (scopeEntity scope) name cls
          chkExport name cls
        exitEdhSTM ets exit cls

    MethodExpr pd@(ProcDecl !addr _ _) ->
      contEdhSTM $ resolveEdhAttrAddr ets addr $ \name -> do
        u <- unsafeIOToSTM newUnique
        let mth = EdhMethod ProcDefi { procedure'uniq = u
                                     , procedure'name = name
                                     , procedure'lexi = Just scope
                                     , procedure'decl = pd
                                     }
        when (addr /= NamedAttr "_") $ do
          if edh'ctx'eff'defining ctx
            then defEffect name mth
            else unless (edh'ctx'pure ctx)
              $ changeEntityAttr ets (scopeEntity scope) name mth
          chkExport name mth
        exitEdhSTM ets exit mth

    GeneratorExpr pd@(ProcDecl !addr _ _) ->
      contEdhSTM $ resolveEdhAttrAddr ets addr $ \name -> do
        u <- unsafeIOToSTM newUnique
        let gdf = EdhGnrtor ProcDefi { procedure'uniq = u
                                     , procedure'name = name
                                     , procedure'lexi = Just scope
                                     , procedure'decl = pd
                                     }
        when (addr /= NamedAttr "_") $ do
          if edh'ctx'eff'defining ctx
            then defEffect name gdf
            else unless (edh'ctx'pure ctx)
              $ changeEntityAttr ets (scopeEntity scope) name gdf
          chkExport name gdf
        exitEdhSTM ets exit gdf

    InterpreterExpr pd@(ProcDecl !addr _ _) ->
      contEdhSTM $ resolveEdhAttrAddr ets addr $ \name -> do
        u <- unsafeIOToSTM newUnique
        let mth = EdhIntrpr ProcDefi { procedure'uniq = u
                                     , procedure'name = name
                                     , procedure'lexi = Just scope
                                     , procedure'decl = pd
                                     }
        when (addr /= NamedAttr "_") $ do
          if edh'ctx'eff'defining ctx
            then defEffect name mth
            else unless (edh'ctx'pure ctx)
              $ changeEntityAttr ets (scopeEntity scope) name mth
          chkExport name mth
        exitEdhSTM ets exit mth

    ProducerExpr pd@(ProcDecl !addr !args _) ->
      contEdhSTM $ resolveEdhAttrAddr ets addr $ \name -> do
        u <- unsafeIOToSTM newUnique
        let mth = EdhPrducr ProcDefi { procedure'uniq = u
                                     , procedure'name = name
                                     , procedure'lexi = Just scope
                                     , procedure'decl = pd
                                     }
        unless (receivesNamedArg "outlet" args) $ throwEdh
          ets
          EvalError
          "a producer procedure should receive a `outlet` keyword argument"
        when (addr /= NamedAttr "_") $ do
          if edh'ctx'eff'defining ctx
            then defEffect name mth
            else unless (edh'ctx'pure ctx)
              $ changeEntityAttr ets (scopeEntity scope) name mth
          chkExport name mth
        exitEdhSTM ets exit mth

    OpDeclExpr !opSym !opPrec opProc@(ProcDecl _ _ !pb) ->
      if edh'ctx'eff'defining ctx
        then throwEdhProc UsageError "Why should an operator be effectful?"
        else case pb of
          -- support re-declaring an existing operator to another name,
          -- with possibly a different precedence
          Left (StmtSrc (_, ExprStmt (AttrExpr (DirectRef (NamedAttr !origOpSym)))))
            -> contEdhSTM $ do
              let
                redeclareOp !origOp = do
                  unless (edh'ctx'pure ctx) $ changeEntityAttr
                    ets
                    (scopeEntity scope)
                    (AttrByName opSym)
                    origOp
                  when (edh'ctx'exporting ctx)
                    $   lookupEntityAttr ets
                                         (objEntity this)
                                         (AttrByName edhExportsMagicName)
                    >>= \case
                          EdhDict (Dict _ !thisExpDS) ->
                            iopdInsert (EdhString opSym) origOp thisExpDS
                          _ -> do
                            d <- EdhDict
                              <$> createEdhDict [(EdhString opSym, origOp)]
                            changeEntityAttr ets
                                             (objEntity this)
                                             (AttrByName edhExportsMagicName)
                                             d
                  exitEdhSTM ets exit origOp
              lookupEdhCtxAttr ets scope (AttrByName origOpSym) >>= \case
                EdhNil ->
                  throwEdh ets EvalError
                    $  "Original operator ("
                    <> origOpSym
                    <> ") not in scope"
                origOp@EdhIntrOp{} -> redeclareOp origOp
                origOp@EdhOprtor{} -> redeclareOp origOp
                val ->
                  throwEdh ets EvalError
                    $  "Can not re-declare a "
                    <> T.pack (edhTypeNameOf val)
                    <> ": "
                    <> T.pack (show val)
                    <> " as an operator"
          _ -> contEdhSTM $ do
            validateOperDecl ets opProc
            u <- unsafeIOToSTM newUnique
            let op = EdhOprtor
                  opPrec
                  Nothing
                  ProcDefi { procedure'uniq = u
                           , procedure'name = AttrByName opSym
                           , procedure'lexi = Just scope
                           , procedure'decl = opProc
                           }
            unless (edh'ctx'pure ctx)
              $ changeEntityAttr ets (scopeEntity scope) (AttrByName opSym) op
            when (edh'ctx'exporting ctx)
              $   lookupEntityAttr ets
                                   (objEntity this)
                                   (AttrByName edhExportsMagicName)
              >>= \case
                    EdhDict (Dict _ !thisExpDS) ->
                      iopdInsert (EdhString opSym) op thisExpDS
                    _ -> do
                      d <- EdhDict <$> createEdhDict [(EdhString opSym, op)]
                      changeEntityAttr ets
                                       (objEntity this)
                                       (AttrByName edhExportsMagicName)
                                       d
            exitEdhSTM ets exit op

    OpOvrdExpr !opSym !opProc !opPrec -> if edh'ctx'eff'defining ctx
      then throwEdhProc UsageError "Why should an operator be effectful?"
      else contEdhSTM $ do
        validateOperDecl ets opProc
        let
          findPredecessor :: STM (Maybe EdhValue)
          findPredecessor =
            lookupEdhCtxAttr ets scope (AttrByName opSym) >>= \case
              EdhNil -> -- do
                -- (EdhConsole logger _) <- readTMVar $ worldConsole world
                -- logger 30 (Just $ sourcePosPretty srcPos)
                --   $ ArgsPack
                --       [EdhString "overriding an unavailable operator"]
                --       odEmpty
                return Nothing
              op@EdhIntrOp{} -> return $ Just op
              op@EdhOprtor{} -> return $ Just op
              opVal          -> do
                (consoleLogger $ worldConsole world)
                    30
                    (Just $ sourcePosPretty srcPos)
                  $ ArgsPack
                      [ EdhString
                        $  "overriding an invalid operator "
                        <> T.pack (edhTypeNameOf opVal)
                        <> ": "
                        <> T.pack (show opVal)
                      ]
                      odEmpty
                return Nothing
        predecessor <- findPredecessor
        u           <- unsafeIOToSTM newUnique
        let op = EdhOprtor
              opPrec
              predecessor
              ProcDefi { procedure'uniq = u
                       , procedure'name = AttrByName opSym
                       , procedure'lexi = Just scope
                       , procedure'decl = opProc
                       }
        unless (edh'ctx'pure ctx)
          $ changeEntityAttr ets (scopeEntity scope) (AttrByName opSym) op
        when (edh'ctx'exporting ctx)
          $   lookupEntityAttr ets
                               (objEntity this)
                               (AttrByName edhExportsMagicName)
          >>= \case
                EdhDict (Dict _ !thisExpDS) ->
                  iopdInsert (EdhString opSym) op thisExpDS
                _ -> do
                  d <- EdhDict <$> createEdhDict [(EdhString opSym, op)]
                  changeEntityAttr ets
                                   (objEntity this)
                                   (AttrByName edhExportsMagicName)
                                   d
        exitEdhSTM ets exit op


    ExportExpr !exps ->
      local
          (const ets
            { edh'context = (edh'context ets) { edh'ctx'exporting = True }
            }
          )
        $ evalExpr exps
        $ \rtn -> local (const ets) $ exitEdhProc' exit rtn


    ImportExpr !argsRcvr !srcExpr !maybeInto -> case maybeInto of
      Nothing        -> importInto (scopeEntity scope) argsRcvr srcExpr exit
      Just !intoExpr -> evalExpr intoExpr $ \(OriginalValue !intoVal _ _) ->
        case intoVal of
          EdhObject !intoObj ->
            importInto (objEntity intoObj) argsRcvr srcExpr exit
          _ ->
            throwEdhProc UsageError
              $  "Can only import into an object, not a "
              <> T.pack (edhTypeNameOf intoVal)

    -- _ -> throwEdhProc EvalError $ "Eval not yet impl for: " <> T.pack (show expr)


validateOperDecl :: EdhThreadState -> ProcDecl -> STM ()
validateOperDecl !ets (ProcDecl _ !op'args _) = case op'args of
  -- 2 pos-args - simple lh/rh value receiving operator
  (PackReceiver [RecvArg _lhName Nothing Nothing, RecvArg _rhName Nothing Nothing])
    -> return ()
  -- 3 pos-args - caller scope + lh/rh expr receiving operator
  (PackReceiver [RecvArg _scopeName Nothing Nothing, RecvArg _lhName Nothing Nothing, RecvArg _rhName Nothing Nothing])
    -> return ()
  _ -> throwEdh ets EvalError "Invalid operator signature"


getEdhAttr :: Expr -> AttrKey -> (EdhValue -> EdhProc) -> EdhExit -> EdhProc
getEdhAttr !fromExpr !key !exitNoAttr !exit = do
  !ets <- ask
  let
    ctx          = edh'context ets
    scope        = contextScope ctx
    this         = thisObject scope
    that         = thatObject scope
    thisObjScope = objectScope ctx this
    chkExit :: Object -> OriginalValue -> STM ()
    chkExit !obj rtn@(OriginalValue !rtnVal _ _) = case rtnVal of
      EdhDescriptor !getter _ ->
        runEdhProc ets $ callEdhMethod obj getter (ArgsPack [] odEmpty) id exit
      _ -> exitEdhSTM' ets exit rtn
    trySelfMagic :: Object -> EdhProc -> EdhProc
    trySelfMagic !obj !noMagic =
      contEdhSTM $ lookupEntityAttr ets (objEntity obj) key >>= \case
        EdhNil ->
          lookupEntityAttr ets (objEntity obj) (AttrByName "@") >>= \case
            EdhNil         -> runEdhProc ets $ noMagic
            EdhMethod !mth -> runEdhProc ets $ callEdhMethod
              obj
              mth
              (ArgsPack [attrKeyValue key] odEmpty)
              id
              exit
            !badMth ->
              throwEdh ets UsageError
                $  "Malformed magic (@) method of "
                <> T.pack (edhTypeNameOf badMth)
        !attrVal -> -- don't shadow an attr directly available from an obj
          chkExit obj $ OriginalValue attrVal (objectScope ctx obj) obj
  case fromExpr of
    -- give super objects the magical power to intercept
    -- attribute access on descendant objects, via `this` ref
    AttrExpr ThisRef ->
      let noMagic :: EdhProc
          noMagic = contEdhSTM $ lookupEdhObjAttr ets this key >>= \case
            EdhNil -> runEdhProc ets $ exitNoAttr $ EdhObject this
            !val   -> chkExit this $ OriginalValue val thisObjScope this
      in  getEdhAttrWSM (AttrByName "@<-")
                        this
                        key
                        (trySelfMagic this noMagic)
                        exit
    -- no super magic layer laid over access via `that` ref
    AttrExpr ThatRef -> contEdhSTM $ lookupEdhObjAttr ets that key >>= \case
      EdhNil ->
        runEdhProc ets $ trySelfMagic that $ exitNoAttr $ EdhObject that
      !val -> chkExit that $ OriginalValue val thisObjScope that
    -- give super objects of an super object the metamagical power to
    -- intercept attribute access on super object, via `super` ref
    AttrExpr SuperRef ->
      let
        noMagic :: EdhProc
        noMagic = contEdhSTM $ lookupEdhSuperAttr ets this key >>= \case
          EdhNil -> runEdhProc ets $ exitNoAttr $ EdhObject this
          !val   -> chkExit this $ OriginalValue val thisObjScope this
        getFromSupers :: [Object] -> EdhProc
        getFromSupers []                   = noMagic
        getFromSupers (super : restSupers) = getEdhAttrWSM
          (AttrByName "@<-^")
          super
          key
          (getFromSupers restSupers)
          exit
      in
        contEdhSTM
        $   readTVar (objSupers this)
        >>= runEdhProc ets
        .   getFromSupers
    _ -> evalExpr fromExpr $ \(OriginalValue !fromVal _ _) ->
      case edhUltimate fromVal of
        EdhObject !obj -> do
          -- give super objects the magical power to intercept
          -- attribute access on descendant objects, via obj ref
          let fromScope = objectScope ctx obj
              noMagic :: EdhProc
              noMagic = contEdhSTM $ lookupEdhObjAttr ets obj key >>= \case
                EdhNil -> runEdhProc ets $ exitNoAttr fromVal
                !val   -> chkExit obj $ OriginalValue val fromScope obj
          getEdhAttrWSM (AttrByName "@<-*")
                        obj
                        key
                        (trySelfMagic obj noMagic)
                        exit

        -- getting attr from an apk
        EdhArgsPack (ArgsPack _ !kwargs) ->
          exitEdhProc exit $ odLookupDefault EdhNil key kwargs

        -- virtual attrs by magic method from context
        !val -> case key of
          AttrByName !attrName -> contEdhSTM $ do
            let !magicName =
                  "__" <> T.pack (edhTypeNameOf val) <> "_" <> attrName <> "__"
            lookupEdhCtxAttr ets scope (AttrByName magicName) >>= \case
              EdhMethod !mth -> runEdhProc ets
                $ callEdhMethod this mth (ArgsPack [val] odEmpty) id exit
              _ -> runEdhProc ets $ exitNoAttr fromVal
          _ -> exitNoAttr fromVal


-- There're 2 tiers of magic happen during object attribute resolution in Edh.
--  *) a magical super controls its direct descendants in behaving as an object, by
--     intercepting the attr resolution
--  *) a metamagical super controls its direct descendants in behaving as a magical
--     super, by intercepting the magic method (as attr) resolution

edhMetaMagicSpell :: AttrKey
edhMetaMagicSpell = AttrByName "!<-"

-- | Try get an attribute from an object, with super magic
getEdhAttrWSM :: AttrKey -> Object -> AttrKey -> EdhProc -> EdhExit -> EdhProc
getEdhAttrWSM !magicSpell !obj !key !exitNoMagic !exit = do
  !ets <- ask
  let
    ctx = edh'context ets
    getViaSupers :: [Object] -> EdhProc
    getViaSupers [] = exitNoMagic
    getViaSupers (super : restSupers) =
      getEdhAttrWSM edhMetaMagicSpell super magicSpell noMetamagic
        $ \(OriginalValue !magicVal !magicScope _) ->
            case edhUltimate magicVal of
              EdhMethod magicMth ->
                contEdhSTM $ withMagicMethod magicScope magicMth
              _ ->
                throwEdhProc EvalError $ "Invalid magic method type: " <> T.pack
                  (edhTypeNameOf magicVal)
     where
      superScope = objectScope ctx super
      noMetamagic :: EdhProc
      noMetamagic =
        contEdhSTM
          $   edhUltimate
          <$> lookupEdhObjAttr ets super magicSpell
          >>= \case
                EdhNil              -> runEdhProc ets $ getViaSupers restSupers
                EdhMethod !magicMth -> withMagicMethod superScope magicMth
                magicVal ->
                  throwEdh ets EvalError
                    $  "Invalid magic method type: "
                    <> T.pack (edhTypeNameOf magicVal)
      withMagicMethod :: Scope -> ProcDefi -> STM ()
      withMagicMethod !magicScope !magicMth =
        runEdhProc ets
          $ callEdhMethod obj magicMth (ArgsPack [attrKeyValue key] odEmpty) id
          $ \(OriginalValue !magicRtn _ _) -> case magicRtn of
              EdhContinue -> getViaSupers restSupers
              _ -> exitEdhProc' exit $ OriginalValue magicRtn magicScope obj
  contEdhSTM $ readTVar (objSupers obj) >>= runEdhProc ets . getViaSupers

-- | Try set an attribute into an object, with super magic
setEdhAttrWSM
  :: EdhThreadState
  -> AttrKey
  -> Object
  -> AttrKey
  -> EdhValue
  -> EdhProc
  -> EdhExit
  -> EdhProc
setEdhAttrWSM !etsAfter !magicSpell !obj !key !val !exitNoMagic !exit = do
  !ets <- ask
  contEdhSTM $ readTVar (objSupers obj) >>= runEdhProc ets . setViaSupers
 where
  setViaSupers :: [Object] -> EdhProc
  setViaSupers []                   = exitNoMagic
  setViaSupers (super : restSupers) = do
    !ets <- ask
    let
      noMetamagic :: EdhProc
      noMetamagic =
        contEdhSTM
          $   edhUltimate
          <$> lookupEdhObjAttr ets super magicSpell
          >>= \case
                EdhNil              -> runEdhProc ets $ setViaSupers restSupers
                EdhMethod !magicMth -> withMagicMethod magicMth
                magicVal ->
                  throwEdh ets EvalError
                    $  "Invalid magic method type: "
                    <> T.pack (edhTypeNameOf magicVal)
      withMagicMethod :: ProcDefi -> STM ()
      withMagicMethod !magicMth =
        runEdhProc ets
          $ callEdhMethod obj
                          magicMth
                          (ArgsPack [attrKeyValue key, val] odEmpty)
                          id
          $ \(OriginalValue !magicRtn _ _) -> case magicRtn of
              EdhContinue -> setViaSupers restSupers
              _           -> local (const etsAfter) $ exitEdhProc exit magicRtn
    getEdhAttrWSM edhMetaMagicSpell super magicSpell noMetamagic
      $ \(OriginalValue !magicVal _ _) -> case edhUltimate magicVal of
          EdhMethod !magicMth -> contEdhSTM $ withMagicMethod magicMth
          _ -> throwEdhProc EvalError $ "Invalid magic method type: " <> T.pack
            (edhTypeNameOf magicVal)


setEdhAttr
  :: EdhThreadState -> Expr -> AttrKey -> EdhValue -> EdhExit -> EdhProc
setEdhAttr !etsAfter !tgtExpr !key !val !exit = do
  !ets <- ask
  let !scope = contextScope $ edh'context ets
      !this  = thisObject scope
      !that  = thatObject scope
  case tgtExpr of
    -- give super objects the magical power to intercept
    -- attribute assignment to descendant objects, via `this` ref
    AttrExpr ThisRef ->
      let noMagic :: EdhProc
          noMagic =
              contEdhSTM $ changeEdhObjAttr ets this key val $ \ !valSet ->
                runEdhProc etsAfter $ exitEdhProc exit valSet
      in  setEdhAttrWSM etsAfter (AttrByName "<-@") this key val noMagic exit
    -- no magic layer laid over assignment via `that` ref
    AttrExpr ThatRef ->
      contEdhSTM $ changeEdhObjAttr ets that key val $ \ !valSet ->
        runEdhProc etsAfter $ exitEdhProc exit valSet
    -- not allowing assignment via super
    AttrExpr SuperRef -> throwEdhProc EvalError "Can not assign via super"
    -- give super objects the magical power to intercept
    -- attribute assignment to descendant objects, via obj ref
    _                 -> evalExpr tgtExpr $ \(OriginalValue !tgtVal _ _) ->
      case edhUltimate tgtVal of
        EdhObject !tgtObj ->
          let noMagic :: EdhProc
              noMagic =
                  contEdhSTM $ changeEdhObjAttr ets tgtObj key val $ \ !valSet ->
                    runEdhProc etsAfter $ exitEdhProc exit valSet
          in  setEdhAttrWSM etsAfter
                            (AttrByName "*<-@")
                            tgtObj
                            key
                            val
                            noMagic
                            exit
        _ ->
          throwEdhProc EvalError
            $  "Invalid assignment target, it's a "
            <> T.pack (edhTypeNameOf tgtVal)
            <> ": "
            <> T.pack (show tgtVal)


edhMakeCall
  :: EdhThreadState
  -> EdhValue
  -> Object
  -> ArgsPacker
  -> (Scope -> Scope)
  -> ((EdhExit -> EdhProc) -> STM ())
  -> STM ()
edhMakeCall !etsCaller !callee'val !callee'that !argsSndr !scopeMod !callMaker
  = case callee'val of
    EdhIntrpr{} -> runEdhProc etsCaller $ packEdhExprs argsSndr $ \apk ->
      contEdhSTM
        $ edhMakeCall' etsCaller callee'val callee'that apk scopeMod callMaker
    _ -> runEdhProc etsCaller $ packEdhArgs argsSndr $ \apk ->
      contEdhSTM
        $ edhMakeCall' etsCaller callee'val callee'that apk scopeMod callMaker

edhMakeCall'
  :: EdhThreadState
  -> EdhValue
  -> Object
  -> ArgsPack
  -> (Scope -> Scope)
  -> ((EdhExit -> EdhProc) -> STM ())
  -> STM ()
edhMakeCall' !etsCaller !callee'val !callee'that apk@(ArgsPack !args !kwargs) !scopeMod !callMaker
  = case callee'val of

    -- calling a class (constructor) procedure
    EdhClass  !cls      -> callMaker $ \exit -> constructEdhObject cls apk exit

    -- calling a method procedure
    EdhMethod !mth'proc -> callMaker
      $ \exit -> callEdhMethod callee'that mth'proc apk scopeMod exit

    -- calling an interpreter procedure
    EdhIntrpr !mth'proc -> do
      -- an Edh interpreter proc needs a `callerScope` as its 1st arg,
      -- while a host interpreter proc doesn't.
      apk' <- case procedure'body $ procedure'decl mth'proc of
        Right _ -> return apk
        Left  _ -> do
          let callerCtx = edh'context etsCaller
          !argCallerScope <- mkScopeWrapper callerCtx $ contextScope callerCtx
          return $ ArgsPack (EdhObject argCallerScope : args) kwargs
      callMaker $ \exit -> callEdhMethod callee'that mth'proc apk' scopeMod exit

    -- calling a producer procedure
    EdhPrducr !mth'proc -> case procedure'body $ procedure'decl mth'proc of
      Right _   -> throwEdh etsCaller EvalError "bug: host producer procedure"
      Left  !pb -> case edhUltimate <$> odLookup (AttrByName "outlet") kwargs of
        Nothing -> do
          outlet <- newEventSink
          callMaker $ \exit -> launchEventProducer exit outlet $ callEdhMethod'
            Nothing
            callee'that
            mth'proc
            pb
            (  ArgsPack args
            $  odFromList
            $  odToList kwargs
            ++ [(AttrByName "outlet", EdhSink outlet)]
            )
            scopeMod
            endOfEdh
        Just (EdhSink !outlet) -> callMaker $ \exit ->
          launchEventProducer exit outlet $ callEdhMethod'
            Nothing
            callee'that
            mth'proc
            pb
            (ArgsPack args kwargs)
            scopeMod
            endOfEdh
        Just !badVal ->
          throwEdh etsCaller UsageError
            $  "The value passed to a producer as `outlet` found to be a "
            <> T.pack (edhTypeNameOf badVal)

    -- calling a generator
    (EdhGnrtor _) -> throwEdh
      etsCaller
      EvalError
      "Can only call a generator method by for-from-do"

    -- calling an object
    (EdhObject !o) ->
      lookupEdhObjAttr etsCaller o (AttrByName "__call__") >>= \case
        EdhMethod !callMth -> callMaker
          $ \exit -> callEdhMethod callee'that callMth apk scopeMod exit
        _ -> throwEdh etsCaller EvalError "No __call__ method on object"

    _ ->
      throwEdh etsCaller EvalError
        $  "Can not call a "
        <> T.pack (edhTypeNameOf callee'val)
        <> ": "
        <> T.pack (show callee'val)


-- | Construct an Edh object from a class
constructEdhObject :: Class -> ArgsPack -> EdhExit -> EdhProc
constructEdhObject !cls apk@(ArgsPack !args !kwargs) !exit = do
  etsCaller <- ask
  createEdhObject cls apk $ \(OriginalValue !thisVal _ _) -> case thisVal of
    EdhObject !this -> do
      let thisEnt     = objEntity this
          callerCtx   = edh'context etsCaller
          callerScope = contextScope callerCtx
          initScope   = callerScope { thisObject  = this
                                    , thatObject  = this
                                    , scopeProc   = cls
                                    , scopeCaller = edh'ctx'stmt callerCtx
                                    }
          ctorCtx = callerCtx
            { edh'ctx'stack      = initScope <| edh'ctx'stack callerCtx
            , edh'ctx'exporting   = False
            , edh'ctx'eff'defining = False
            }
          etsCtor = etsCaller { edh'context = ctorCtx }
      contEdhSTM
        $   lookupEntityAttr etsCtor thisEnt (AttrByName "__init__")
        >>= \case
              EdhNil ->
                if (null args && odNull kwargs) -- no ctor arg at all
                   || -- it's okay for a host class to omit __init__()
                        -- while processes ctor args by the host class proc
                      isRight (procedure'body $ procedure'decl cls)
                then
                  exitEdhSTM etsCaller exit thisVal
                else
                  throwEdh etsCaller EvalError
                  $  "No __init__() defined by class "
                  <> procedureName cls
                  <> " to receive argument(s)"
              EdhMethod !initMth ->
                case procedure'body $ procedure'decl initMth of
                  Right !hp ->
                    runEdhProc etsCtor
                      $ hp apk
                      $ \(OriginalValue !hostInitRtn _ _) ->
                          -- a host __init__() method is responsible to return new
                          -- `this` explicitly, or another value as appropriate
                          contEdhSTM $ exitEdhSTM etsCaller exit hostInitRtn
                  Left !pb ->
                    runEdhProc etsCaller
                      $ local (const etsCtor)
                      $ callEdhMethod' Nothing this initMth pb apk id
                      $ \(OriginalValue !initRtn _ _) ->
                          local (const etsCaller) $ case initRtn of
                              -- allow a __init__() procedure to explicitly return other
                              -- value than newly constructed `this` object
                              -- it can still `return this` to early stop the proc
                              -- which is magically an advanced feature
                            EdhReturn !rtnVal -> exitEdhProc exit rtnVal
                            EdhContinue       -> throwEdhProc
                              EvalError
                              "Unexpected continue from __init__()"
                            -- allow the use of `break` to early stop a __init__() 
                            -- procedure with nil result
                            EdhBreak -> exitEdhProc exit nil
                            -- no explicit return from __init__() procedure, return the
                            -- newly constructed this object, throw away the last
                            -- value from the procedure execution
                            _        -> exitEdhProc exit thisVal
              badInitMth ->
                throwEdh etsCaller EvalError
                  $  "Invalid __init__() method type from class - "
                  <> T.pack (edhTypeNameOf badInitMth)
    _ -> -- return whatever the constructor returned if not an object
      exitEdhProc exit thisVal

-- | Creating an Edh object from a class, without calling its `__init__()` method
createEdhObject :: Class -> ArgsPack -> EdhExit -> EdhProc
createEdhObject !cls !apk !exit = do
  etsCaller <- ask
  let !callerCtx   = edh'context etsCaller
      !callerScope = contextScope callerCtx
  case procedure'body $ procedure'decl cls of

    -- calling a host class (constructor) procedure
    Right !hp -> contEdhSTM $ do
      -- note: cross check logic here with `mkHostClass`
      -- the host ctor procedure is responsible for instance creation, so the
      -- scope entiy, `this` and `that` are not changed for its call frame
      let !calleeScope = callerScope { scopeProc   = cls
                                     , scopeCaller = edh'ctx'stmt callerCtx
                                     }
          !calleeCtx = callerCtx
            { edh'ctx'stack      = calleeScope <| edh'ctx'stack callerCtx
            , generatorCaller    = Nothing
            , edh'ctx'match      = true
            , edh'ctx'pure        = False
            , edh'ctx'exporting   = False
            , edh'ctx'eff'defining = False
            }
          !etsCallee = etsCaller { edh'context = calleeCtx }
      runEdhProc etsCallee $ hp apk $ \(OriginalValue !val _ _) ->
        contEdhSTM $ exitEdhSTM etsCaller exit val

    -- calling an Edh namespace/class (constructor) procedure
    Left !pb -> contEdhSTM $ do
      newEnt  <- createHashEntity =<< iopdEmpty
      newThis <- viewAsEdhObject newEnt cls []
      let
        goCtor = do
          let !ctorScope = objectScope callerCtx newThis
              !ctorCtx   = callerCtx
                { edh'ctx'stack      = ctorScope <| edh'ctx'stack callerCtx
                , generatorCaller    = Nothing
                , edh'ctx'match      = true
                , edh'ctx'pure        = False
                , edh'ctx'stmt       = pb
                , edh'ctx'exporting   = False
                , edh'ctx'eff'defining = False
                }
              !etsCtor = etsCaller { edh'context = ctorCtx }
          runEdhProc etsCtor $ evalStmt pb $ \(OriginalValue !ctorRtn _ _) ->
            local (const etsCaller) $ case ctorRtn of
              -- allow a class procedure to explicitly return other
              -- value than newly constructed `this` object
              -- it can still `return this` to early stop the proc
              -- which is magically an advanced feature
              EdhReturn !rtnVal -> exitEdhProc exit rtnVal
              EdhContinue ->
                throwEdhProc EvalError "Unexpected continue from constructor"
              -- allow the use of `break` to early stop a constructor 
              -- procedure with nil result
              EdhBreak -> exitEdhProc exit nil
              -- no explicit return from class procedure, return the
              -- newly constructed this object, throw away the last
              -- value from the procedure execution
              _        -> exitEdhProc exit (EdhObject newThis)
      case procedure'args $ procedure'decl cls of
        -- a namespace procedure, should pass ctor args to it
        WildReceiver -> do
          let !recvCtx = callerCtx
                { edh'ctx'stack = (lexicalScopeOf cls) { thisObject = newThis
                                                       , thatObject = newThis
                                                       }
                                    :| []
                , generatorCaller    = Nothing
                , edh'ctx'match      = true
                , edh'ctx'pure        = False
                , edh'ctx'stmt       = pb
                , edh'ctx'exporting   = False
                , edh'ctx'eff'defining = False
                }
          runEdhProc etsCaller $ recvEdhArgs recvCtx WildReceiver apk $ \oed ->
            contEdhSTM $ do
              updateEntityAttrs etsCaller (objEntity newThis) $ odToList oed
              goCtor
        -- a class procedure, should leave ctor args for its __init__ method
        PackReceiver [] -> goCtor
        _               -> error "bug: imposible constructor procedure args"


callEdhOperator
  :: Object -> ProcDefi -> Maybe EdhValue -> [EdhValue] -> EdhExit -> EdhProc
callEdhOperator !mth'that !mth'proc !prede !args !exit = do
  etsCaller <- ask
  let callerCtx   = edh'context etsCaller
      callerScope = contextScope callerCtx
  case procedure'body $ procedure'decl mth'proc of

    -- calling a host operator procedure
    Right !hp -> do
      -- a host procedure views the same scope entity as of the caller's
      -- call frame
      let !mthScope = (lexicalScopeOf mth'proc) { scopeEntity = scopeEntity
                                                  callerScope
                                                , thatObject  = mth'that
                                                , scopeProc   = mth'proc
                                                , scopeCaller = edh'ctx'stmt
                                                  callerCtx
                                                }
          !mthCtx = callerCtx
            { edh'ctx'stack      = mthScope <| edh'ctx'stack callerCtx
            , generatorCaller    = Nothing
            , edh'ctx'match      = true
            , edh'ctx'pure        = False
            , edh'ctx'exporting   = False
            , edh'ctx'eff'defining = False
            }
          !etsMth = etsCaller { edh'context = mthCtx }
      -- push stack for the host procedure
      local (const etsMth)
        $ hp (ArgsPack args odEmpty)
        $ \(OriginalValue !val _ _) ->
        -- pop stack after host procedure returned
        -- return whatever the result a host procedure returned
            contEdhSTM $ exitEdhSTM etsCaller exit val

    -- calling an Edh operator procedure
    Left !pb ->
      callEdhOperator' Nothing mth'that mth'proc prede pb args
        $ \(OriginalValue !mthRtn _ _) -> case mthRtn of
            -- allow continue to be return from a operator proc,
            -- to carry similar semantics like `NotImplemented` in Python
            EdhContinue      -> exitEdhProc exit EdhContinue
            -- allow the use of `break` to early stop a operator 
            -- procedure with nil result
            EdhBreak         -> exitEdhProc exit nil
            -- explicit return
            EdhReturn rtnVal -> exitEdhProc exit rtnVal
            -- no explicit return, assuming it returns the last
            -- value from procedure execution
            _                -> exitEdhProc exit mthRtn

callEdhOperator'
  :: Maybe EdhGenrCaller
  -> Object
  -> ProcDefi
  -> Maybe EdhValue
  -> StmtSrc
  -> [EdhValue]
  -> EdhExit
  -> EdhProc
callEdhOperator' !gnr'caller !callee'that !mth'proc !prede !mth'body !args !exit
  = do
    !etsCaller <- ask
    let
      !callerCtx = edh'context etsCaller
      !recvCtx   = callerCtx
        { edh'ctx'stack = (lexicalScopeOf mth'proc) { thatObject = callee'that }
                            :| []
        , generatorCaller    = Nothing
        , edh'ctx'match      = true
        , edh'ctx'stmt       = mth'body
        , edh'ctx'pure        = False
        , edh'ctx'exporting   = False
        , edh'ctx'eff'defining = False
        }
    recvEdhArgs recvCtx
                (procedure'args $ procedure'decl mth'proc)
                (ArgsPack args odEmpty)
      $ \ !ed -> contEdhSTM $ do
          ent <- createHashEntity =<< iopdFromList (odToList ed)
          let !mthScope = (lexicalScopeOf mth'proc)
                { scopeEntity = ent
                , thatObject  = callee'that
                , scopeProc   = mth'proc
                , scopeCaller = edh'ctx'stmt callerCtx
                }
              !mthCtx = callerCtx
                { edh'ctx'stack      = mthScope <| edh'ctx'stack callerCtx
                , generatorCaller    = gnr'caller
                , edh'ctx'match      = true
                , edh'ctx'stmt       = mth'body
                , edh'ctx'pure        = False
                , edh'ctx'exporting   = False
                , edh'ctx'eff'defining = False
                }
              !etsMth = etsCaller { edh'context = mthCtx }
          case prede of
            Nothing -> pure ()
            -- put the overridden predecessor operator in scope of the overriding
            -- op proc's run ctx
            Just !predOp ->
              changeEntityAttr etsMth ent (procedure'name mth'proc) predOp
          -- push stack for the Edh procedure
          runEdhProc etsMth
            $ evalStmt mth'body
            $ \(OriginalValue !mthRtn _ _) ->
            -- pop stack after Edh procedure returned
                local (const etsCaller) $ exitEdhProc exit mthRtn


callEdhMethod
  :: Object -> ProcDefi -> ArgsPack -> (Scope -> Scope) -> EdhExit -> EdhProc
callEdhMethod !mth'that !mth'proc !apk !scopeMod !exit = do
  etsCaller <- ask
  let callerCtx   = edh'context etsCaller
      callerScope = contextScope callerCtx
  case procedure'body $ procedure'decl mth'proc of

    -- calling a host method procedure
    Right !hp -> do
      -- a host procedure views the same scope entity as of the caller's
      -- call frame
      let !mthScope = scopeMod $ (lexicalScopeOf mth'proc)
            { scopeEntity = scopeEntity callerScope
            , thatObject  = mth'that
            , scopeProc   = mth'proc
            , scopeCaller = edh'ctx'stmt callerCtx
            }
          !mthCtx = callerCtx
            { edh'ctx'stack      = mthScope <| edh'ctx'stack callerCtx
            , generatorCaller    = Nothing
            , edh'ctx'match      = true
            , edh'ctx'pure        = False
            , edh'ctx'exporting   = False
            , edh'ctx'eff'defining = False
            }
          !etsMth = etsCaller { edh'context = mthCtx }
      -- push stack for the host procedure
      local (const etsMth) $ hp apk $ \(OriginalValue !val _ _) ->
        -- pop stack after host procedure returned
        -- return whatever the result a host procedure returned
        contEdhSTM $ exitEdhSTM etsCaller exit val

    -- calling an Edh method procedure
    Left !pb ->
      callEdhMethod' Nothing mth'that mth'proc pb apk scopeMod
        $ \(OriginalValue !mthRtn _ _) -> case mthRtn of
            -- allow continue to be return from a method proc,
            -- to carry similar semantics like `NotImplemented` in Python
            EdhContinue      -> exitEdhProc exit EdhContinue
            -- allow the use of `break` to early stop a method 
            -- procedure with nil result
            EdhBreak         -> exitEdhProc exit nil
            -- explicit return
            EdhReturn rtnVal -> exitEdhProc exit rtnVal
            -- no explicit return, assuming it returns the last
            -- value from procedure execution
            _                -> exitEdhProc exit mthRtn

callEdhMethod'
  :: Maybe EdhGenrCaller
  -> Object
  -> ProcDefi
  -> StmtSrc
  -> ArgsPack
  -> (Scope -> Scope)
  -> EdhExit
  -> EdhProc
callEdhMethod' !gnr'caller !callee'that !mth'proc !mth'body !apk !scopeMod !exit
  = do
    !etsCaller <- ask
    let
      !callerCtx = edh'context etsCaller
      !recvCtx   = callerCtx
        { edh'ctx'stack = (lexicalScopeOf mth'proc) { thatObject = callee'that }
                            :| []
        , generatorCaller    = Nothing
        , edh'ctx'match      = true
        , edh'ctx'stmt       = mth'body
        , edh'ctx'pure        = False
        , edh'ctx'exporting   = False
        , edh'ctx'eff'defining = False
        }
    recvEdhArgs recvCtx (procedure'args $ procedure'decl mth'proc) apk $ \ed ->
      contEdhSTM $ do
        ent <- createHashEntity =<< iopdFromList (odToList ed)
        let !mthScope = scopeMod $ (lexicalScopeOf mth'proc)
              { scopeEntity = ent
              , thatObject  = callee'that
              , scopeProc   = mth'proc
              , scopeCaller = edh'ctx'stmt callerCtx
              }
            !mthCtx = callerCtx
              { edh'ctx'stack      = mthScope <| edh'ctx'stack callerCtx
              , generatorCaller    = gnr'caller
              , edh'ctx'match      = true
              , edh'ctx'stmt       = mth'body
              , edh'ctx'pure        = False
              , edh'ctx'exporting   = False
              , edh'ctx'eff'defining = False
              }
            !etsMth = etsCaller { edh'context = mthCtx }
        -- push stack for the Edh procedure
        runEdhProc etsMth $ evalStmt mth'body $ \(OriginalValue !mthRtn _ _) ->
          -- pop stack after Edh procedure returned
          local (const etsCaller) $ exitEdhProc exit mthRtn


edhForLoop
  :: EdhThreadState
  -> ArgsReceiver
  -> Expr
  -> Expr
  -> (EdhValue -> STM ())
  -> ((EdhExit -> EdhProc) -> STM ())
  -> STM ()
edhForLoop !etsLooper !argsRcvr !iterExpr !doExpr !iterCollector !forLooper =
  do
    let
        -- receive one yielded value from the generator, the 'genrCont' here is
        -- to continue the generator execution, result passed to the 'genrCont'
        -- here is the eval'ed value of the `yield` expression from the
        -- generator's perspective, or exception to be thrown from there
      recvYield
        :: EdhExit
        -> EdhValue
        -> (Either (EdhThreadState, EdhValue) EdhValue -> STM ())
        -> EdhProc
      recvYield !exit !yielded'val !genrCont = do
        ets <- ask
        let
          !ctx   = edh'context ets
          !scope = contextScope ctx
          doOne !etsTry !exit' =
            runEdhProc etsTry
              $ recvEdhArgs
                  (edh'context etsTry)
                  argsRcvr
                  (case yielded'val of
                    EdhArgsPack apk -> apk
                    _               -> ArgsPack [yielded'val] odEmpty
                  )
              $ \em -> contEdhSTM $ do
                  updateEntityAttrs etsTry (scopeEntity scope) $ odToList em
                  runEdhProc etsTry $ evalExpr doExpr exit'
          doneOne (OriginalValue !doResult _ _) =
            case edhDeCaseClose doResult of
              EdhContinue ->
                -- send nil to generator on continue
                contEdhSTM $ genrCont $ Right nil
              EdhBreak ->
                -- break out of the for-from-do loop,
                -- the generator on <break> yielded will return
                -- nil, effectively have the for loop eval to nil
                contEdhSTM $ genrCont $ Right EdhBreak
              EdhCaseOther ->
                -- send nil to generator on no-match of a branch
                contEdhSTM $ genrCont $ Right nil
              EdhFallthrough ->
                -- send nil to generator on fallthrough
                contEdhSTM $ genrCont $ Right nil
              EdhReturn EdhReturn{} -> -- this has special meaning
                -- Edh code should not use this pattern
                throwEdhProc UsageError "double return from do-of-for?"
              EdhReturn !rtnVal ->
                -- early return from for-from-do, the geneerator on
                -- double wrapped return yielded, will unwrap one
                -- level and return the result, effectively have the
                -- for loop eval to return that 
                contEdhSTM $ genrCont $ Right $ EdhReturn $ EdhReturn rtnVal
              !val -> contEdhSTM $ do
                -- vanilla val from do, send to generator
                iterCollector val
                genrCont $ Right val
        case yielded'val of
          EdhNil -> -- nil yielded from a generator effectively early stops
            exitEdhProc exit nil
          EdhContinue -> throwEdhProc EvalError "generator yielded continue"
          EdhBreak    -> throwEdhProc EvalError "generator yielded break"
          EdhReturn{} -> throwEdhProc EvalError "generator yielded return"
          _ ->
            contEdhSTM
              $ edhCatch ets doOne doneOne
              $ \ !etsThrower !exv _recover rethrow -> case exv of
                  EdhNil -> rethrow -- no exception occurred in do block
                  _ -> -- exception uncaught in do block
                    -- propagate to the generator, the genr may catch it or 
                    -- the exception will propagate to outer of for-from-do
                    genrCont $ Left (etsThrower, exv)

    runEdhProc etsLooper $ case deParen iterExpr of
      CallExpr !procExpr !argsSndr -> -- loop over a generator
        contEdhSTM
          $ resolveEdhCallee etsLooper procExpr
          $ \(OriginalValue !callee'val _ !callee'that, scopeMod) ->
              runEdhProc etsLooper $ case callee'val of

                -- calling a generator
                (EdhGnrtor !gnr'proc) -> packEdhArgs argsSndr $ \apk ->
                  case procedure'body $ procedure'decl gnr'proc of

                    -- calling a host generator
                    Right !hp -> contEdhSTM $ forLooper $ \exit -> do
                      ets <- ask
                      let !ctx   = edh'context ets
                          !scope = contextScope ctx
                      contEdhSTM $ do
                        -- a host procedure views the same scope entity as of the caller's
                        -- call frame
                        let !calleeScope = (lexicalScopeOf gnr'proc)
                              { scopeEntity = scopeEntity scope
                              , thatObject  = callee'that
                              , scopeProc   = gnr'proc
                              , scopeCaller = edh'ctx'stmt ctx
                              }
                            !calleeCtx = ctx
                              { edh'ctx'stack = calleeScope <| edh'ctx'stack ctx
                              , generatorCaller    = Just (ets, recvYield exit)
                              , edh'ctx'match      = true
                              , edh'ctx'pure        = False
                              , edh'ctx'exporting   = False
                              , edh'ctx'eff'defining = False
                              }
                            !etsCallee = ets { edh'context = calleeCtx }
                        -- insert a cycle tick here, so if no tx required for the call
                        -- overall, the callee resolution tx stops here then the callee
                        -- runs in next stm transaction
                        flip (exitEdhSTM' etsCallee) (wuji etsCallee) $ \_ ->
                          hp apk $ \(OriginalValue val _ _) ->
                            -- return the result in CPS with caller ets restored
                            contEdhSTM $ exitEdhSTM etsLooper exit val

                    -- calling an Edh generator
                    Left !pb -> contEdhSTM $ forLooper $ \exit -> do
                      ets <- ask
                      callEdhMethod' (Just (ets, recvYield exit))
                                     callee'that
                                     gnr'proc
                                     pb
                                     apk
                                     scopeMod
                        $ \(OriginalValue !gnrRtn _ _) -> case gnrRtn of
                            -- return the result in CPS with looper ets restored
                            EdhContinue ->
                              -- propagate the continue from generator return
                              contEdhSTM $ exitEdhSTM etsLooper exit EdhContinue
                            EdhBreak ->
                              -- todo what's the case a generator would break out?
                              contEdhSTM $ exitEdhSTM etsLooper exit nil
                            EdhReturn !rtnVal -> -- it'll be double return, in
                              -- case do block issued return and propagated here
                              -- or the generator can make it that way, which is
                              -- black magic
                              -- unwrap the return, as result of this for-loop 
                              contEdhSTM $ exitEdhSTM etsLooper exit rtnVal
                            -- otherwise passthrough
                            _ -> contEdhSTM $ exitEdhSTM etsLooper exit gnrRtn

                -- calling other procedures, assume to loop over its return value
                _ ->
                  contEdhSTM
                    $ edhMakeCall etsLooper
                                  callee'val
                                  callee'that
                                  argsSndr
                                  scopeMod
                    $ \mkCall ->
                        runEdhProc etsLooper
                          $ mkCall
                          $ \(OriginalValue !iterVal _ _) ->
                              loopOverValue iterVal

      _ -> -- loop over an iterable value
           evalExpr iterExpr $ \(OriginalValue !iterVal _ _) ->
        loopOverValue $ edhDeCaseClose iterVal

 where

  loopOverValue :: EdhValue -> EdhProc
  loopOverValue !iterVal = contEdhSTM $ forLooper $ \exit -> do
    ets <- ask
    let !ctx   = edh'context ets
        !scope = contextScope ctx
    contEdhSTM $ do
      let -- do one iteration
          do1 :: ArgsPack -> STM () -> STM ()
          do1 !apk !next =
            runEdhProc ets $ recvEdhArgs ctx argsRcvr apk $ \em ->
              contEdhSTM $ do
                updateEntityAttrs ets (scopeEntity scope) $ odToList em
                runEdhProc ets
                  $ evalExpr doExpr
                  $ \(OriginalValue !doResult _ _) -> case doResult of
                      EdhBreak ->
                        -- break for loop
                        exitEdhProc exit nil
                      rtn@EdhReturn{} ->
                        -- early return during for loop
                        exitEdhProc exit rtn
                      _ -> contEdhSTM $ do
                        -- continue for loop
                        iterCollector doResult
                        next

          -- loop over a series of args packs
          iterThem :: [ArgsPack] -> STM ()
          iterThem []           = exitEdhSTM ets exit nil
          iterThem (apk : apks) = do1 apk $ iterThem apks

          -- loop over a subscriber's channel of an event sink
          iterEvt :: TChan EdhValue -> STM ()
          iterEvt !subChan = edhPerformSTM ets (readTChan subChan) $ \case
            EdhNil -> -- nil marks end-of-stream from an event sink
              exitEdhProc exit nil -- stop the for-from-do loop
            EdhArgsPack apk -> contEdhSTM $ do1 apk $ iterEvt subChan
            v -> contEdhSTM $ do1 (ArgsPack [v] odEmpty) $ iterEvt subChan

      case edhUltimate iterVal of

        -- loop from an event sink
        (EdhSink sink) -> subscribeEvents sink >>= \(subChan, mrv) ->
          case mrv of
            Nothing -> iterEvt subChan
            Just ev -> case ev of
              EdhNil -> -- this sink is already marked at end-of-stream
                exitEdhSTM ets exit nil
              EdhArgsPack apk -> do1 apk $ iterEvt subChan
              v               -> do1 (ArgsPack [v] odEmpty) $ iterEvt subChan

        -- loop from a positonal-only args pack
        (EdhArgsPack (ArgsPack !args !kwargs)) | odNull kwargs -> iterThem
          [ case val of
              EdhArgsPack apk' -> apk'
              _                -> ArgsPack [val] odEmpty
          | val <- args
          ]

        -- loop from a keyword-only args pack
        (EdhArgsPack (ArgsPack !args !kwargs)) | null args -> iterThem
          [ ArgsPack [attrKeyValue k, v] odEmpty | (k, v) <- odToList kwargs ]

        -- loop from a list
        (EdhList (List _ !l)) -> do
          ll <- readTVar l
          iterThem
            [ case val of
                EdhArgsPack apk' -> apk'
                _                -> ArgsPack [val] odEmpty
            | val <- ll
            ]

        -- loop from a dict
        (EdhDict (Dict _ !d)) -> do
          del <- iopdToList d
          -- don't be tempted to yield pairs from a dict here,
          -- it'll be messy if some entry values are themselves pairs
          iterThem [ ArgsPack [k, v] odEmpty | (k, v) <- del ]

        -- TODO define the magic method for an object to be able to respond
        --      to for-from-do looping

        _ ->
          throwEdh etsLooper EvalError
            $  "Can not do a for loop from "
            <> T.pack (edhTypeNameOf iterVal)
            <> ": "
            <> T.pack (show iterVal)


-- | Create a reflective object capturing the specified scope as from the
-- specified context
--
-- the edh'ctx'stmt is captured as the procedure body of its fake class
--
-- todo currently only lexical context is recorded, the call frames may
--      be needed in the future
mkScopeWrapper :: Context -> Scope -> STM Object
mkScopeWrapper !ctx !scope = do
  -- a scope wrapper object is itself a mao object, no attr at all
  wrapperEnt <- createMaoEntity
  -- 'scopeSuper' provides the builtin scope manipulation methods
  viewAsEdhObject wrapperEnt wrapperClass [scopeSuper world]
 where
  !world        = contextWorld ctx
  !wrapperClass = (objClass $ scopeSuper world)
    { procedure'lexi = Just scope
    , procedure'decl = procedure'decl $ scopeProc scope
    }

isScopeWrapper :: Context -> Object -> STM Bool
isScopeWrapper !ctx !o = do
  supers <- readTVar (objSupers o)
  return $ elem (scopeSuper world) supers
  where !world = contextWorld ctx

-- | Get the wrapped scope from a wrapper object
wrappedScopeOf :: Object -> Scope
wrappedScopeOf !sw = case procedure'lexi $ objClass sw of
  Just !scope -> scope
  Nothing     -> error "bug: wrapped scope lost"


-- | Assign an evaluated value to a target expression
--
-- Note the calling procedure should declare in-tx state in evaluating the
-- right-handle value as well as running this, so the evaluation of the
-- right-hand value as well as the writting to the target entity are done
-- within the same tx, thus for atomicity of the whole assignment.
assignEdhTarget :: EdhThreadState -> Expr -> EdhExit -> EdhValue -> EdhProc
assignEdhTarget !etsAfter !lhExpr !exit !rhVal = do
  !ets <- ask
  let !ctx  = edh'context ets
      scope = contextScope ctx
      this  = thisObject scope
      that  = thatObject scope
      exitWithChkExportTo :: Entity -> AttrKey -> EdhValue -> STM ()
      exitWithChkExportTo !ent !artKey !artVal = do
        when (edh'ctx'exporting ctx)
          $   lookupEntityAttr ets ent (AttrByName edhExportsMagicName)
          >>= \case
                EdhDict (Dict _ !thisExpDS) ->
                  iopdInsert (attrKeyValue artKey) artVal thisExpDS
                _ -> do
                  d <- EdhDict <$> createEdhDict [(attrKeyValue artKey, artVal)]
                  changeEntityAttr ets
                                   (objEntity this)
                                   (AttrByName edhExportsMagicName)
                                   d
        runEdhProc etsAfter $ exitEdhProc exit artVal
      defEffectInto :: Entity -> AttrKey -> STM ()
      defEffectInto !ent !artKey =
        lookupEntityAttr ets ent (AttrByName edhEffectsMagicName) >>= \case
          EdhDict (Dict _ !effDS) ->
            iopdInsert (attrKeyValue artKey) rhVal effDS
          _ -> do
            d <- EdhDict <$> createEdhDict [(attrKeyValue artKey, rhVal)]
            changeEntityAttr ets ent (AttrByName edhEffectsMagicName) d
  case lhExpr of
    AttrExpr !addr -> case addr of
      -- silently drop value assigned to single underscore
      DirectRef (NamedAttr "_") ->
        contEdhSTM $ runEdhProc etsAfter $ exitEdhProc exit nil
      -- no magic imposed to direct assignment in a (possibly class) proc
      DirectRef !addr' -> contEdhSTM $ resolveEdhAttrAddr ets addr' $ \key ->
        do
          if edh'ctx'eff'defining ctx
            then defEffectInto (scopeEntity scope) key
            else changeEntityAttr ets (scopeEntity scope) key rhVal
          exitWithChkExportTo (objEntity this) key rhVal
      -- special case, assigning with `this.v=x` `that.v=y`, handle exports and
      -- effect definition
      IndirectRef (AttrExpr ThisRef) addr' ->
        contEdhSTM $ resolveEdhAttrAddr ets addr' $ \key -> do
          let !thisEnt = objEntity this
          if edh'ctx'eff'defining ctx
            then do
              defEffectInto thisEnt key
              exitWithChkExportTo thisEnt key rhVal
            else changeEdhObjAttr ets this key rhVal
              $ \ !valSet -> exitWithChkExportTo thisEnt key valSet
      IndirectRef (AttrExpr ThatRef) addr' ->
        contEdhSTM $ resolveEdhAttrAddr ets addr' $ \key -> do
          let !thatEnt = objEntity $ thatObject scope
          if edh'ctx'eff'defining ctx
            then do
              defEffectInto thatEnt key
              exitWithChkExportTo thatEnt key rhVal
            else changeEdhObjAttr ets that key rhVal
              $ \ !valSet -> exitWithChkExportTo thatEnt key valSet
      -- assign to an addressed attribute
      IndirectRef !tgtExpr !addr' ->
        contEdhSTM $ resolveEdhAttrAddr ets addr' $ \key ->
          runEdhProc ets $ setEdhAttr etsAfter tgtExpr key rhVal exit
      -- god forbidden things
      ThisRef  -> throwEdhProc EvalError "Can not assign to this"
      ThatRef  -> throwEdhProc EvalError "Can not assign to that"
      SuperRef -> throwEdhProc EvalError "Can not assign to super"
    -- dereferencing attribute assignment
    InfixExpr "@" !tgtExpr !addrRef ->
      evalExpr addrRef $ \(OriginalValue !addrVal _ _) ->
        case edhUltimate addrVal of
          EdhExpr _ (AttrExpr (DirectRef !addr)) _ ->
            contEdhSTM $ resolveEdhAttrAddr ets addr $ \key ->
              runEdhProc ets $ setEdhAttr etsAfter tgtExpr key rhVal exit
          EdhString !attrName ->
            setEdhAttr etsAfter tgtExpr (AttrByName attrName) rhVal exit
          EdhSymbol !sym ->
            setEdhAttr etsAfter tgtExpr (AttrBySym sym) rhVal exit
          _ ->
            throwEdhProc EvalError
              $  "Invalid attribute reference type - "
              <> T.pack (edhTypeNameOf addrVal)
    x ->
      throwEdhProc EvalError
        $  "Invalid left hand expression for assignment: "
        <> T.pack (show x)


changeEdhObjAttr
  :: EdhThreadState
  -> Object
  -> AttrKey
  -> EdhValue
  -> (EdhValue -> STM ())
  -> STM ()
changeEdhObjAttr !ets !obj !key !val !exit =
  -- don't shadow overwriting to a directly existing attr
  lookupEntityAttr ets (objEntity obj) key >>= \case
    EdhNil -> lookupEntityAttr ets (objEntity obj) (AttrByName "@=") >>= \case
      EdhNil ->
        -- normal attr lookup with supers involved
        lookupEdhObjAttr ets obj key >>= chkProperty
      EdhMethod !mth ->
        -- call magic (@=) method
        runEdhProc ets
          $ callEdhMethod obj mth (ArgsPack [attrKeyValue key, val] odEmpty) id
          $ \(OriginalValue !rtnVal _ _) -> contEdhSTM $ exit rtnVal
      !badMth ->
        throwEdh ets UsageError $ "Malformed magic (@=) method of " <> T.pack
          (edhTypeNameOf badMth)
    !existingVal ->
      -- a directly existing attr, bypassed magic (@=) method
      chkProperty existingVal
 where
  chkProperty = \case
    EdhDescriptor !getter Nothing ->
      throwEdh ets UsageError
        $  "Property "
        <> T.pack (show $ procedure'name getter)
        <> " is readonly"
    EdhDescriptor _ (Just !setter) ->
      let !args = case val of
            EdhNil -> []
            _      -> [val]
      in  runEdhProc ets
            $ callEdhMethod obj setter (ArgsPack args odEmpty) id
            $ \(OriginalValue !propRtn _ _) -> contEdhSTM $ exit propRtn
    _ -> do
      changeEntityAttr ets (objEntity obj) key val
      exit val


-- The Edh call convention is so called call-by-repacking, i.e. a new pack of
-- arguments are evaluated & packed at the calling site, then passed to the
-- callee site, where arguments in the pack are received into an entity to be
-- used as the run-scope of the callee, the receiving may include re-packing
-- into attributes manifested for rest-args. For any argument mentioned by
-- the callee but missing from the pack from the caller, the call should fail
-- if the callee did not specify a default expr for the missing arg; if the
-- callee did have a default expr specified, the default expr should be eval'ed
-- in the callee's lexial context to provide the missing value into the entity
-- with attr name of that arg.

-- This is semantically much the same as Python's call convention, regarding
-- positional and keyword argument matching, in addition with the following:
--  * wildcard receiver - receive all keyword arguments into the entity
--  * retargeting - don't receive the argument into the entity, but assign
--    to an attribute of another object, typically `this` object in scope
--  * argument renaming - match the name as sent, receive to a differently
--     named attribute of the entity. while renaming a positional argument
--     is doable but meaningless, you'd just use the later name for the arg
--  * rest-args repacking, in forms of:
--     *args
--     **kwargs
--     ***apk


recvEdhArgs
  :: Context
  -> ArgsReceiver
  -> ArgsPack
  -> (OrderedDict AttrKey EdhValue -> EdhProc)
  -> EdhProc
recvEdhArgs !recvCtx !argsRcvr apk@(ArgsPack !posArgs !kwArgs) !exit = do
  !etsCaller <- ask
  let -- args receive always done in callee's context with tx on
    !etsRecv = etsCaller { edh'in'tx = True, edh'context = recvCtx }
    recvFromPack
      :: ArgsPack
      -> IOPD AttrKey EdhValue
      -> ArgReceiver
      -> (ArgsPack -> STM ())
      -> STM ()
    recvFromPack pk@(ArgsPack !posArgs' !kwArgs') !em !argRcvr !exit' =
      case argRcvr of
        RecvRestPosArgs "_" ->
          -- silently drop the value to single underscore, while consume the args
          -- from incoming pack
          exit' (ArgsPack [] kwArgs')
        RecvRestPosArgs !restPosArgAttr -> do
          iopdInsert (AttrByName restPosArgAttr)
                     (EdhArgsPack $ ArgsPack posArgs' odEmpty)
                     em
          exit' (ArgsPack [] kwArgs')
        RecvRestKwArgs "_" ->
          -- silently drop the value to single underscore, while consume the args
          -- from incoming pack
          exit' (ArgsPack posArgs' odEmpty)
        RecvRestKwArgs restKwArgAttr -> if T.null restKwArgAttr
          then do
            iopdUpdate (odToList kwArgs') em
            exit' (ArgsPack posArgs' odEmpty)
          else do
            iopdInsert (AttrByName restKwArgAttr)
                       (EdhArgsPack $ ArgsPack [] kwArgs')
                       em
            exit' (ArgsPack posArgs' odEmpty)
        RecvRestPkArgs "_" ->
          -- silently drop the value to single underscore, while consume the args
          -- from incoming pack
          exit' (ArgsPack [] odEmpty)
        RecvRestPkArgs restPkArgAttr -> do
          iopdInsert (AttrByName restPkArgAttr) (EdhArgsPack pk) em
          exit' (ArgsPack [] odEmpty)
        RecvArg (NamedAttr "_") _ _ ->
          -- silently drop the value to single underscore, while consume the arg
          -- from incoming pack
          resolveArgValue (AttrByName "_") Nothing
            $ \(_, posArgs'', kwArgs'') -> exit' (ArgsPack posArgs'' kwArgs'')
        RecvArg !argAddr !argTgtAddr !argDefault ->
          resolveEdhAttrAddr etsRecv argAddr $ \argKey ->
            resolveArgValue argKey argDefault
              $ \(argVal, posArgs'', kwArgs'') -> case argTgtAddr of
                  Nothing -> do
                    iopdInsert argKey argVal em
                    exit' (ArgsPack posArgs'' kwArgs'')
                  Just (DirectRef addr) -> case addr of
                    NamedAttr "_" -> -- drop
                      exit' (ArgsPack posArgs'' kwArgs'')
                    NamedAttr attrName -> do -- simple rename
                      iopdInsert (AttrByName attrName) argVal em
                      exit' (ArgsPack posArgs'' kwArgs'')
                    SymbolicAttr symName -> -- todo support this ?
                      throwEdh etsRecv UsageError
                        $  "Do you mean `this.@"
                        <> symName
                        <> "` instead ?"
                  Just addr@(IndirectRef _ _) -> do
                    -- do assignment in callee's context, and return to caller's afterwards
                    runEdhProc etsRecv $ assignEdhTarget etsCaller
                                                         (AttrExpr addr)
                                                         endOfEdh
                                                         argVal
                    exit' (ArgsPack posArgs'' kwArgs'')
                  tgt ->
                    throwEdh etsRecv UsageError
                      $  "Invalid argument retarget: "
                      <> T.pack (show tgt)
     where
      resolveArgValue
        :: AttrKey
        -> Maybe Expr
        -> (  (EdhValue, [EdhValue], OrderedDict AttrKey EdhValue)
           -> STM ()
           )
        -> STM ()
      resolveArgValue !argKey !argDefault !exit'' = do
        let (inKwArgs, kwArgs'') = odTakeOut argKey kwArgs'
        case inKwArgs of
          Just argVal -> exit'' (argVal, posArgs', kwArgs'')
          _           -> case posArgs' of
            (posArg : posArgs'') -> exit'' (posArg, posArgs'', kwArgs'')
            []                   -> case argDefault of
              Just defaultExpr -> do
                defaultVar <- newEmptyTMVar
                -- always eval the default value atomically in callee's contex
                runEdhProc etsRecv $ evalExpr
                  defaultExpr
                  (\(OriginalValue !val _ _) ->
                    contEdhSTM (putTMVar defaultVar $ edhDeCaseClose val)
                  )
                defaultVal <- readTMVar defaultVar
                exit'' (defaultVal, posArgs', kwArgs'')
              _ ->
                throwEdh etsCaller UsageError $ "Missing argument: " <> T.pack
                  (show argKey)
    woResidual :: ArgsPack -> STM () -> STM ()
    woResidual (ArgsPack !posResidual !kwResidual) !exit'
      | not (null posResidual)
      = throwEdh etsCaller UsageError
        $  "Extraneous "
        <> T.pack (show $ length posResidual)
        <> " positional argument(s)"
      | not (odNull kwResidual)
      = throwEdh etsCaller UsageError
        $  "Extraneous keyword arguments: "
        <> T.pack (unwords (show <$> odKeys kwResidual))
      | otherwise
      = exit'
    doReturn :: OrderedDict AttrKey EdhValue -> STM ()
    doReturn !es =
      -- insert a cycle tick here, so if no tx required for the call
      -- overall, the args receiving tx stops here then the callee
      -- runs in next stm transaction
      exitEdhSTM' etsCaller (\_ -> exit es) (wuji etsCaller)

  -- execution of the args receiving always in a tx for atomicity, and
  -- in the specified receiving (should be callee's outer) context
  local (const etsRecv) $ case argsRcvr of
    PackReceiver argRcvrs -> contEdhSTM $ iopdEmpty >>= \ !em ->
      let
        go :: [ArgReceiver] -> ArgsPack -> STM ()
        go [] !apk' = woResidual apk' $ iopdSnapshot em >>= doReturn
        go (r : rest) !apk' =
          recvFromPack apk' em r $ \ !apk'' -> go rest apk''
      in
        go argRcvrs apk
    SingleReceiver argRcvr -> contEdhSTM $ iopdEmpty >>= \ !em ->
      recvFromPack apk em argRcvr
        $ \ !apk' -> woResidual apk' $ iopdSnapshot em >>= doReturn
    WildReceiver -> contEdhSTM $ if null posArgs
      then doReturn kwArgs
      else
        throwEdh etsRecv EvalError
        $  "Unexpected "
        <> T.pack (show $ length posArgs)
        <> " positional argument(s) to wild receiver"


-- | Pack args as expressions, normally in preparation of calling another
-- interpreter procedure
packEdhExprs :: ArgsPacker -> (ArgsPack -> EdhProc) -> EdhProc
packEdhExprs !pkrs !pkExit = ask >>= \ !ets -> contEdhSTM $ do
  kwIOPD <- iopdEmpty
  let
    pkExprs :: [ArgSender] -> ([EdhValue] -> EdhProc) -> EdhProc
    pkExprs []       !exit = exit []
    pkExprs (x : xs) !exit = case x of
      UnpackPosArgs _ ->
        throwEdhProc EvalError "unpack to expr not supported yet"
      UnpackKwArgs _ ->
        throwEdhProc EvalError "unpack to expr not supported yet"
      UnpackPkArgs _ ->
        throwEdhProc EvalError "unpack to expr not supported yet"
      SendPosArg !argExpr -> pkExprs xs $ \ !posArgs -> contEdhSTM $ do
        !xu <- unsafeIOToSTM newUnique
        runEdhProc ets $ exit (EdhExpr xu argExpr "" : posArgs)
      SendKwArg !kwAddr !argExpr ->
        contEdhSTM $ resolveEdhAttrAddr ets kwAddr $ \ !kwKey -> do
          xu <- unsafeIOToSTM newUnique
          iopdInsert kwKey (EdhExpr xu argExpr "") kwIOPD
          runEdhProc ets $ pkExprs xs $ \ !posArgs' -> exit posArgs'
  runEdhProc ets $ pkExprs pkrs $ \ !args ->
    contEdhSTM $ iopdSnapshot kwIOPD >>= \ !kwargs ->
      runEdhProc ets $ pkExit $ ArgsPack args kwargs


-- | Pack args as caller, normally in preparation of calling another procedure
packEdhArgs :: ArgsPacker -> (ArgsPack -> EdhProc) -> EdhProc
packEdhArgs !argSenders !pkExit = ask >>= \ets -> contEdhSTM $ do
  let !etsPacking = ets
        {
          -- make sure values in a pack are evaluated in same tx
          edh'in'tx   = True
        , edh'context = (edh'context ets) {
          -- discourage artifact definition during args packing
                                            edh'ctx'pure = True }
        }
  !kwIOPD <- iopdEmpty
  let
    pkArgs :: [ArgSender] -> ([EdhValue] -> EdhProc) -> EdhProc
    pkArgs []       !exit = exit []
    pkArgs (x : xs) !exit = do
      let
        edhVal2Kw :: EdhValue -> STM () -> (AttrKey -> STM ()) -> STM ()
        edhVal2Kw !k !nopExit !exit' = case k of
          EdhString !name -> exit' $ AttrByName name
          EdhSymbol !sym  -> exit' $ AttrBySym sym
          _               -> nopExit
        dictKvs2Kwl
          :: [(ItemKey, EdhValue)]
          -> ([(AttrKey, EdhValue)] -> STM ())
          -> STM ()
        dictKvs2Kwl !ps !exit' = go ps []         where
          go :: [(ItemKey, EdhValue)] -> [(AttrKey, EdhValue)] -> STM ()
          go [] !kvl = exit' kvl
          go ((k, v) : rest) !kvl =
            edhVal2Kw k (go rest kvl) $ \ !k' -> go rest ((k', v) : kvl)
      case x of
        UnpackPosArgs !posExpr ->
          evalExpr posExpr $ \(OriginalValue !val _ _) ->
            case edhUltimate val of
              (EdhArgsPack (ArgsPack !posArgs _kwArgs)) ->
                pkArgs xs $ \ !posArgs' -> exit (posArgs ++ posArgs')
              (EdhPair !k !v) ->
                pkArgs xs $ \ !posArgs -> exit ([k, noneNil v] ++ posArgs)
              (EdhList (List _ !l)) -> pkArgs xs $ \ !posArgs ->
                contEdhSTM $ do
                  ll <- readTVar l
                  runEdhProc ets $ exit ((noneNil <$> ll) ++ posArgs)
              _ ->
                throwEdhProc EvalError
                  $  "Can not unpack args from a "
                  <> T.pack (edhTypeNameOf val)
                  <> ": "
                  <> T.pack (show val)
        UnpackKwArgs !kwExpr -> evalExpr kwExpr $ \(OriginalValue !val _ _) ->
          case edhUltimate val of
            EdhArgsPack (ArgsPack _posArgs !kwArgs') -> contEdhSTM $ do
              iopdUpdate (odToList kwArgs') kwIOPD
              runEdhProc etsPacking $ pkArgs xs $ \ !posArgs' -> exit posArgs'
            (EdhPair !k !v) ->
              contEdhSTM
                $ edhVal2Kw
                    k
                    (  throwEdh ets UsageError
                    $  "Invalid keyword type: "
                    <> T.pack (edhTypeNameOf k)
                    )
                $ \ !kw -> do
                    iopdInsert kw (noneNil $ edhDeCaseClose v) kwIOPD
                    runEdhProc etsPacking $ pkArgs xs $ \ !posArgs ->
                      exit posArgs
            (EdhDict (Dict _ !ds)) -> contEdhSTM $ do
              !dkvl <- iopdToList ds
              dictKvs2Kwl dkvl $ \ !kvl -> do
                iopdUpdate kvl kwIOPD
                runEdhProc etsPacking $ pkArgs xs $ \ !posArgs -> exit posArgs
            _ ->
              throwEdhProc EvalError
                $  "Can not unpack kwargs from a "
                <> T.pack (edhTypeNameOf val)
                <> ": "
                <> T.pack (show val)
        UnpackPkArgs !pkExpr -> evalExpr pkExpr $ \(OriginalValue !val _ _) ->
          case edhUltimate val of
            (EdhArgsPack (ArgsPack !posArgs !kwArgs')) -> contEdhSTM $ do
              iopdUpdate (odToList kwArgs') kwIOPD
              runEdhProc etsPacking $ pkArgs xs $ \ !posArgs' ->
                exit (posArgs ++ posArgs')
            _ ->
              throwEdhProc EvalError
                $  "Can not unpack apk from a "
                <> T.pack (edhTypeNameOf val)
                <> ": "
                <> T.pack (show val)
        SendPosArg !argExpr -> evalExpr argExpr $ \(OriginalValue !val _ _) ->
          pkArgs xs
            $ \ !posArgs -> exit (noneNil (edhDeCaseClose val) : posArgs)
        SendKwArg !kwAddr !argExpr ->
          evalExpr argExpr $ \(OriginalValue !val _ _) -> case kwAddr of
            NamedAttr "_" ->  -- silently drop the value to keyword of single
              -- underscore, the user may just want its side-effect
              pkArgs xs $ \ !posArgs -> exit posArgs
            _ -> contEdhSTM $ resolveEdhAttrAddr ets kwAddr $ \ !kwKey -> do
              iopdInsert kwKey (noneNil $ edhDeCaseClose val) kwIOPD
              runEdhProc ets $ pkArgs xs $ \ !posArgs -> exit posArgs
  runEdhProc etsPacking $ pkArgs argSenders $ \ !posArgs -> contEdhSTM $ do
    !kwArgs <- iopdSnapshot kwIOPD
    -- restore original tx state after args packed
    runEdhProc ets $ pkExit $ ArgsPack posArgs kwArgs


val2DictEntry
  :: EdhThreadState -> EdhValue -> ((ItemKey, EdhValue) -> STM ()) -> STM ()
val2DictEntry _ (EdhPair !k !v) !exit = exit (k, v)
val2DictEntry _ (EdhArgsPack (ArgsPack [!k, !v] !kwargs)) !exit
  | odNull kwargs = exit (k, v)
val2DictEntry !ets !val _ = throwEdh
  ets
  UsageError
  ("Invalid entry for dict " <> T.pack (edhTypeNameOf val) <> ": " <> T.pack
    (show val)
  )

pvlToDict :: EdhThreadState -> [EdhValue] -> (DictStore -> STM ()) -> STM ()
pvlToDict !ets !pvl !exit = do
  !ds <- iopdEmpty
  let go []         = exit ds
      go (p : rest) = val2DictEntry ets p $ \(!key, !val) -> do
        iopdInsert key val ds
        go rest
  go pvl

pvlToDictEntries
  :: EdhThreadState -> [EdhValue] -> ([(ItemKey, EdhValue)] -> STM ()) -> STM ()
pvlToDictEntries !ets !pvl !exit = do
  let go !entries [] = exit entries
      go !entries (p : rest) =
        val2DictEntry ets p $ \ !entry -> go (entry : entries) rest
  go [] $ reverse pvl


edhValueNull :: EdhThreadState -> EdhValue -> (Bool -> STM ()) -> STM ()
edhValueNull _    EdhNil                   !exit = exit True
edhValueNull !ets (EdhNamedValue _ v     ) !exit = edhValueNull ets v exit
edhValueNull _ (EdhDecimal d) !exit = exit $ D.decimalIsNaN d || d == 0
edhValueNull _    (EdhBool    b          ) !exit = exit $ not b
edhValueNull _    (EdhString  s          ) !exit = exit $ T.null s
edhValueNull _    (EdhSymbol  _          ) !exit = exit False
edhValueNull _    (EdhDict    (Dict _ ds)) !exit = iopdNull ds >>= exit
edhValueNull _    (EdhList    (List _ l )) !exit = null <$> readTVar l >>= exit
edhValueNull _ (EdhArgsPack (ArgsPack args kwargs)) !exit =
  exit $ null args && odNull kwargs
edhValueNull _ (EdhExpr _ (LitExpr NilLiteral) _) !exit = exit True
edhValueNull _ (EdhExpr _ (LitExpr (DecLiteral d)) _) !exit =
  exit $ D.decimalIsNaN d || d == 0
edhValueNull _ (EdhExpr _ (LitExpr (BoolLiteral b)) _) !exit = exit b
edhValueNull _ (EdhExpr _ (LitExpr (StringLiteral s)) _) !exit =
  exit $ T.null s
edhValueNull !ets (EdhObject !o) !exit =
  lookupEdhObjAttr ets o (AttrByName "__null__") >>= \case
    EdhNil -> exit False
    EdhMethod !nulMth ->
      runEdhProc ets
        $ callEdhMethod o nulMth (ArgsPack [] odEmpty) id
        $ \(OriginalValue nulVal _ _) -> contEdhSTM $ case nulVal of
            EdhBool isNull -> exit isNull
            _              -> edhValueNull ets nulVal exit
    EdhBool !b -> exit b
    badVal ->
      throwEdh ets UsageError $ "Invalid value type from __null__: " <> T.pack
        (edhTypeNameOf badVal)
edhValueNull _ _ !exit = exit False


edhIdentEqual :: EdhValue -> EdhValue -> Bool
edhIdentEqual (EdhNamedValue x'n x'v) (EdhNamedValue y'n y'v) =
  x'n == y'n && edhIdentEqual x'v y'v
edhIdentEqual EdhNamedValue{} _               = False
edhIdentEqual _               EdhNamedValue{} = False
edhIdentEqual x               y               = x == y

edhNamelyEqual
  :: EdhThreadState -> EdhValue -> EdhValue -> (Bool -> STM ()) -> STM ()
edhNamelyEqual !ets (EdhNamedValue !x'n !x'v) (EdhNamedValue !y'n !y'v) !exit =
  if x'n /= y'n then exit False else edhNamelyEqual ets x'v y'v exit
edhNamelyEqual _ EdhNamedValue{} _               !exit = exit False
edhNamelyEqual _ _               EdhNamedValue{} !exit = exit False
edhNamelyEqual !ets !x !y !exit =
  -- it's considered namely not equal if can not trivially concluded, i.e.
  -- may need to invoke magic methods or sth.
  edhValueEqual ets x y $ exit . fromMaybe False

edhValueEqual
  :: EdhThreadState -> EdhValue -> EdhValue -> (Maybe Bool -> STM ()) -> STM ()
edhValueEqual !ets !lhVal !rhVal !exit =
  let
    lhv = edhUltimate lhVal
    rhv = edhUltimate rhVal
  in
    if lhv == rhv
      then -- identity equal
           exit $ Just True
      else case lhv of
        EdhList (List _ lhll) -> case rhv of
          EdhList (List _ rhll) -> do
            lhl <- readTVar lhll
            rhl <- readTVar rhll
            cmp2List lhl rhl $ exit . Just
          _ -> exit $ Just False
        EdhDict (Dict _ !lhd) -> case rhv of
          EdhDict (Dict _ !rhd) -> do
            lhl <- iopdToList lhd
            rhl <- iopdToList rhd
            -- regenerate the entry lists with HashMap to elide diffs in
            -- entry order
            cmp2Map (Map.toList $ Map.fromList lhl)
                    (Map.toList $ Map.fromList rhl)
              $ exit
              . Just
          _ -> exit $ Just False
        -- don't conclude it if either of the two is an object, so magic
        -- methods can get the chance to be invoked
        -- there may be some magic to be invoked and some may even return
        -- vectorized result
        EdhObject{} -> exit Nothing
        _           -> case rhv of
          EdhObject{} -> exit Nothing
          -- neither is object, not equal for sure
          _           -> exit $ Just False
 where
  cmp2List :: [EdhValue] -> [EdhValue] -> (Bool -> STM ()) -> STM ()
  cmp2List []      []      !exit' = exit' True
  cmp2List (_ : _) []      !exit' = exit' False
  cmp2List []      (_ : _) !exit' = exit' False
  cmp2List (lhVal' : lhRest) (rhVal' : rhRest) !exit' =
    edhValueEqual ets lhVal' rhVal' $ \case
      Just True -> cmp2List lhRest rhRest exit'
      _         -> exit' False
  cmp2Map
    :: [(ItemKey, EdhValue)]
    -> [(ItemKey, EdhValue)]
    -> (Bool -> STM ())
    -> STM ()
  cmp2Map []      []      !exit' = exit' True
  cmp2Map (_ : _) []      !exit' = exit' False
  cmp2Map []      (_ : _) !exit' = exit' False
  cmp2Map ((lhKey, lhVal') : lhRest) ((rhKey, rhVal') : rhRest) !exit' =
    if lhKey /= rhKey
      then exit' False
      else edhValueEqual ets lhVal' rhVal' $ \case
        Just True -> cmp2Map lhRest rhRest exit'
        _         -> exit' False


-- comma separated repr string
_edhCSR :: [Text] -> [EdhValue] -> EdhExit -> EdhProc
_edhCSR reprs [] !exit =
  exitEdhProc exit $ EdhString $ T.concat [ i <> ", " | i <- reverse reprs ]
_edhCSR reprs (v : rest) !exit =
  edhValueReprProc v $ \(OriginalValue r _ _) -> case r of
    EdhString repr -> _edhCSR (repr : reprs) rest exit
    _              -> error "bug: edhValueReprProc returned non-string in CPS"
-- comma separated repr string for kwargs
_edhKwArgsCSR :: [(Text, Text)] -> [(AttrKey, EdhValue)] -> EdhExit -> EdhProc
_edhKwArgsCSR !entries [] !exit' = exitEdhProc exit' $ EdhString $ T.concat
  [ k <> "=" <> v <> ", " | (k, v) <- entries ]
_edhKwArgsCSR !entries ((k, v) : rest) exit' =
  edhValueReprProc v $ \(OriginalValue r _ _) -> case r of
    EdhString repr ->
      _edhKwArgsCSR ((T.pack (show k), repr) : entries) rest exit'
    _ -> error "bug: edhValueReprProc returned non-string in CPS"
-- comma separated repr string for dict entries
_edhDictCSR :: [(Text, Text)] -> [(EdhValue, EdhValue)] -> EdhExit -> EdhProc
_edhDictCSR entries [] !exit' = exitEdhProc exit' $ EdhString $ T.concat
  [ k <> ":" <> v <> ", " | (k, v) <- entries ]
_edhDictCSR entries ((k, v) : rest) exit' =
  edhValueReprProc k $ \(OriginalValue kr _ _) -> case kr of
    EdhString !kRepr -> do
      let krDecor :: Text -> Text
          krDecor = case k of
            -- quote the key repr in the entry if it's a term
            -- bcoz (:=) precedence is 1, less than (:)'s 2
            EdhNamedValue{} -> \r -> "(" <> r <> ")"
            _               -> id
          vrDecor :: Text -> Text
          vrDecor = case v of
            -- quote the value repr in the entry if it's a pair
            EdhPair{} -> \r -> "(" <> r <> ")"
            _         -> id
      edhValueReprProc v $ \(OriginalValue vr _ _) -> case vr of
        EdhString !vRepr ->
          _edhDictCSR ((krDecor kRepr, vrDecor vRepr) : entries) rest exit'
        _ -> error "bug: edhValueReprProc returned non-string in CPS"
    _ -> error "bug: edhValueReprProc returned non-string in CPS"

edhValueRepr :: EdhThreadState -> EdhValue -> (Text -> STM ()) -> STM ()
edhValueRepr !ets !val !exit =
  runEdhProc ets $ edhValueReprProc val $ \(OriginalValue vr _ _) -> case vr of
    EdhString !r -> contEdhSTM $ exit r
    _            -> error "bug: edhValueReprProc returned non-string"

edhValueReprProc :: EdhValue -> EdhExit -> EdhProc

-- pair repr
edhValueReprProc (EdhPair v1 v2) !exit =
  edhValueReprProc v1 $ \(OriginalValue r1 _ _) -> case r1 of
    EdhString repr1 -> edhValueReprProc v2 $ \(OriginalValue r2 _ _) ->
      case r2 of
        EdhString repr2 -> exitEdhProc exit $ EdhString $ repr1 <> ":" <> repr2
        _ -> error "bug: edhValueReprProc returned non-string in CPS"
    _ -> error "bug: edhValueReprProc returned non-string in CPS"

-- apk repr
edhValueReprProc (EdhArgsPack (ArgsPack !args !kwargs)) !exit
  | null args && odNull kwargs = exitEdhProc exit $ EdhString "()"
  | otherwise = _edhCSR [] args $ \(OriginalValue argsR _ _) -> case argsR of
    EdhString argsCSR ->
      _edhKwArgsCSR [] (odToReverseList kwargs)
        $ \(OriginalValue kwargsR _ _) -> case kwargsR of
            EdhString kwargsCSR ->
              exitEdhProc exit $ EdhString $ "( " <> argsCSR <> kwargsCSR <> ")"
            _ -> error "bug: edhValueReprProc returned non-string in CPS"
    _ -> error "bug: edhValueReprProc returned non-string in CPS"

-- list repr
edhValueReprProc (EdhList (List _ ls)) !exit = do
  ets <- ask
  contEdhSTM $ readTVar ls >>= \vs -> if null vs
    then -- no space should show in an empty list
         exitEdhSTM ets exit $ EdhString "[]"
    else runEdhProc ets $ _edhCSR [] vs $ \(OriginalValue csr _ _) ->
      case csr of
        -- advocate trailing comma here
        EdhString !csRepr ->
          exitEdhProc exit $ EdhString $ "[ " <> csRepr <> "]"
        _ -> error "bug: edhValueReprProc returned non-string in CPS"

-- dict repr
edhValueReprProc (EdhDict (Dict _ !ds)) !exit = do
  ets <- ask
  contEdhSTM $ iopdNull ds >>= \case
    True -> -- no space should show in an empty dict
      exitEdhSTM ets exit $ EdhString "{}"
    False -> iopdToReverseList ds >>= \ !entries ->
      runEdhProc ets
        $ _edhDictCSR [] entries
        $ \(OriginalValue entriesR _ _) -> case entriesR of
            EdhString entriesCSR ->
              exitEdhProc exit $ EdhString $ "{ " <> entriesCSR <> "}"
            _ -> error "bug: edhValueReprProc returned non-string in CPS"

-- object repr
edhValueReprProc (EdhObject !o) !exit = do
  ets <- ask
  contEdhSTM $ lookupEdhObjAttr ets o (AttrByName "__repr__") >>= \case
    EdhNil           -> exitEdhSTM ets exit $ EdhString $ T.pack $ show o
    repr@EdhString{} -> exitEdhSTM ets exit repr
    EdhMethod !reprMth ->
      runEdhProc ets
        $ callEdhMethod o reprMth (ArgsPack [] odEmpty) id
        $ \(OriginalValue reprVal _ _) -> case reprVal of
            s@EdhString{} -> exitEdhProc exit s
            _             -> edhValueReprProc reprVal exit
    reprVal -> runEdhProc ets $ edhValueReprProc reprVal exit

-- repr of named value
edhValueReprProc (EdhNamedValue !n v@EdhNamedValue{}) !exit =
  -- Edh operators are all left-associative, parenthesis needed
  edhValueReprProc v $ \(OriginalValue r _ _) -> case r of
    EdhString repr ->
      exitEdhProc exit $ EdhString $ n <> " := (" <> repr <> ")"
    _ -> error "bug: edhValueReprProc returned non-string in CPS"
edhValueReprProc (EdhNamedValue !n !v) !exit =
  edhValueReprProc v $ \(OriginalValue r _ _) -> case r of
    EdhString repr -> exitEdhProc exit $ EdhString $ n <> " := " <> repr
    _              -> error "bug: edhValueReprProc returned non-string in CPS"

-- repr of other values simply as to show itself
edhValueReprProc !v !exit = exitEdhProc exit $ EdhString $ T.pack $ show v


edhValueStr :: EdhValue -> EdhExit -> EdhProc
edhValueStr s@EdhString{} !exit' = exitEdhProc exit' s
edhValueStr !v            !exit' = edhValueReprProc v exit'


withThatEntity
  :: forall a . Typeable a => (EdhThreadState -> a -> STM ()) -> EdhProc
withThatEntity = withThatEntity'
  $ \ !ets -> throwEdh ets UsageError "bug: unexpected entity storage type"
withThatEntity'
  :: forall a
   . Typeable a
  => (EdhThreadState -> STM ())
  -> (EdhThreadState -> a -> STM ())
  -> EdhProc
withThatEntity' !naExit !exit = ask >>= \ !ets ->
  contEdhSTM
    $   fromDynamic
    <$> readTVar
          (entity'store $ objEntity $ thatObject $ contextScope $ edh'context
            ets
          )
    >>= \case
          Nothing   -> naExit ets

          Just !esd -> exit ets esd

withEntityOfClass
  :: forall a
   . Typeable a
  => Unique
  -> (EdhThreadState -> a -> STM ())
  -> EdhProc
withEntityOfClass !classUniq = withEntityOfClass' classUniq
  $ \ !ets -> throwEdh ets UsageError "bug: unexpected entity storage type"
withEntityOfClass'
  :: forall a
   . Typeable a
  => Unique
  -> (EdhThreadState -> STM ())
  -> (EdhThreadState -> a -> STM ())
  -> EdhProc
withEntityOfClass' !classUniq !naExit !exit = ask >>= \ !ets -> contEdhSTM $ do
  let !that = thatObject $ contextScope $ edh'context ets
  resolveEdhInstance ets classUniq that >>= \case
    Nothing -> naExit ets
    Just !inst ->
      fromDynamic <$> readTVar (entity'store $ objEntity inst) >>= \case
        Nothing   -> naExit ets

        Just !esd -> exit ets esd


modifyThatEntity
  :: forall a
   . Typeable a
  => EdhExit
  -> (EdhThreadState -> a -> (a -> EdhValue -> STM ()) -> STM ())
  -> EdhProc
modifyThatEntity !exit !esMod = modifyThatEntity'
  (\ !ets -> throwEdh ets UsageError "bug: unexpected heavy entity storage type"
  )
  exit
  esMod
modifyThatEntity'
  :: forall a
   . Typeable a
  => (EdhThreadState -> STM ())
  -> EdhExit
  -> (EdhThreadState -> a -> (a -> EdhValue -> STM ()) -> STM ())
  -> EdhProc
modifyThatEntity' !naExit !exit !esMod = ask >>= \ !ets -> contEdhSTM $ do
  let !esv =
        entity'store $ objEntity $ thatObject $ contextScope $ edh'context ets
  fromDynamic <$> readTVar esv >>= \case
    Nothing                -> naExit ets
    Just (esmv :: TMVar a) -> do
      !esd <- takeTMVar esmv
      let tryAct !ets' !exit' = esMod ets' esd $ \ !esd' !exitVal -> do
            putTMVar esmv esd'
            exitEdhSTM ets' exit' exitVal
      edhCatch ets tryAct exit $ \_etsThrower _exv _recover rethrow -> do
        void $ tryPutTMVar esmv esd
        rethrow

modifyEntityOfClass
  :: forall a
   . Typeable a
  => Unique
  -> EdhExit
  -> (EdhThreadState -> a -> (a -> EdhValue -> STM ()) -> STM ())
  -> EdhProc
modifyEntityOfClass !classUniq !exit !esMod = modifyEntityOfClass'
  classUniq
  (\ !ets -> throwEdh ets UsageError "bug: unexpected heavy entity storage type"
  )
  exit
  esMod
modifyEntityOfClass'
  :: forall a
   . Typeable a
  => Unique
  -> (EdhThreadState -> STM ())
  -> EdhExit
  -> (EdhThreadState -> a -> (a -> EdhValue -> STM ()) -> STM ())
  -> EdhProc
modifyEntityOfClass' !classUniq !naExit !exit !esMod = ask >>= \ !ets ->
  contEdhSTM $ do
    let !that = thatObject $ contextScope $ edh'context ets
    resolveEdhInstance ets classUniq that >>= \case
      Nothing    -> naExit ets
      Just !inst -> do
        let !esv = entity'store $ objEntity inst
        fromDynamic <$> readTVar esv >>= \case
          Nothing                -> naExit ets
          Just (esmv :: TMVar a) -> do
            !esd <- takeTMVar esmv
            let tryAct !ets' !exit' = esMod ets' esd $ \ !esd' !exitVal -> do
                  putTMVar esmv esd'
                  exitEdhSTM ets' exit' exitVal
            edhCatch ets tryAct exit $ \_etsThrower _exv _recover rethrow -> do
              void $ tryPutTMVar esmv esd
              rethrow


resolveEdhCallee
  :: EdhThreadState
  -> Expr
  -> ((OriginalValue, Scope -> Scope) -> STM ())
  -> STM ()
resolveEdhCallee !ets !expr !exit = case expr of
  PerformExpr !effAddr -> resolveEdhAttrAddr ets effAddr $ \ !effKey ->
    resolveEdhEffCallee ets effKey edhTargetStackForPerform exit
  BehaveExpr !effAddr -> resolveEdhAttrAddr ets effAddr
    $ \ !effKey -> resolveEdhEffCallee ets effKey edhTargetStackForBehave exit
  _ -> runEdhProc ets $ evalExpr expr $ \ov@(OriginalValue !v _ _) ->
    contEdhSTM $ exit (ov { valueFromOrigin = edhDeCaseClose v }, id)

resolveEdhEffCallee
  :: EdhThreadState
  -> AttrKey
  -> (EdhThreadState -> [Scope])
  -> ((OriginalValue, Scope -> Scope) -> STM ())
  -> STM ()
resolveEdhEffCallee !ets !effKey !targetStack !exit =
  resolveEffectfulAttr ets (targetStack ets) (attrKeyValue effKey) >>= \case
    Just (!effArt, !outerStack) -> exit
      ( OriginalValue effArt scope $ thisObject scope
      , \ !procScope -> procScope { effectsStack = outerStack }
      )
    Nothing ->
      throwEdh ets UsageError $ "No such effect: " <> T.pack (show effKey)
  where !scope = contextScope $ edh'context ets

edhTargetStackForPerform :: EdhThreadState -> [Scope]
edhTargetStackForPerform !ets = case effectsStack scope of
  []         -> NE.tail $ edh'ctx'stack ctx
  outerStack -> outerStack
 where
  !ctx   = edh'context ets
  !scope = contextScope ctx

edhTargetStackForBehave :: EdhThreadState -> [Scope]
edhTargetStackForBehave !ets = NE.tail $ edh'ctx'stack ctx
  where !ctx = edh'context ets

resolveEdhPerform :: EdhThreadState -> AttrKey -> (EdhValue -> STM ()) -> STM ()
resolveEdhPerform !ets !effKey !exit =
  resolveEffectfulAttr ets (edhTargetStackForPerform ets) (attrKeyValue effKey)
    >>= \case
          Just (!effArt, _) -> exit effArt
          Nothing ->
            throwEdh ets UsageError $ "No such effect: " <> T.pack (show effKey)

resolveEdhBehave :: EdhThreadState -> AttrKey -> (EdhValue -> STM ()) -> STM ()
resolveEdhBehave !ets !effKey !exit =
  resolveEffectfulAttr ets (edhTargetStackForBehave ets) (attrKeyValue effKey)
    >>= \case
          Just (!effArt, _) -> exit effArt
          Nothing ->
            throwEdh ets UsageError $ "No such effect: " <> T.pack (show effKey)


parseEdhIndex
  :: EdhThreadState -> EdhValue -> (Either Text EdhIndex -> STM ()) -> STM ()
parseEdhIndex !ets !val !exit = case val of

  -- empty  
  EdhArgsPack (ArgsPack [] !kwargs') | odNull kwargs' -> exit $ Right EdhAll

  -- term
  EdhNamedValue "All" _ -> exit $ Right EdhAll
  EdhNamedValue "Any" _ -> exit $ Right EdhAny
  EdhNamedValue _ !termVal -> parseEdhIndex ets termVal exit

  -- range 
  EdhPair (EdhPair !startVal !stopVal) !stepVal -> sliceNum startVal $ \case
    Left  !err   -> exit $ Left err
    Right !start -> sliceNum stopVal $ \case
      Left  !err  -> exit $ Left err
      Right !stop -> sliceNum stepVal $ \case
        Left  !err -> exit $ Left err
        Right step -> exit $ Right $ EdhSlice start stop step
  EdhPair !startVal !stopVal -> sliceNum startVal $ \case
    Left  !err   -> exit $ Left err
    Right !start -> sliceNum stopVal $ \case
      Left  !err  -> exit $ Left err
      Right !stop -> exit $ Right $ EdhSlice start stop Nothing

  -- single
  _ -> sliceNum val $ \case
    Right Nothing   -> exit $ Right EdhAll
    Right (Just !i) -> exit $ Right $ EdhIndex i
    Left  !err      -> exit $ Left err

 where
  sliceNum :: EdhValue -> (Either Text (Maybe Int) -> STM ()) -> STM ()
  sliceNum !val' !exit' = case val' of

    -- number
    EdhDecimal !idxNum -> case D.decimalToInteger idxNum of
      Just !i -> exit' $ Right $ Just $ fromInteger i
      _ ->
        exit'
          $  Left
          $  "An integer expected as index number but given: "
          <> T.pack (show idxNum)

    -- term
    EdhNamedValue "All" _        -> exit' $ Right Nothing
    EdhNamedValue "Any" _        -> exit' $ Right Nothing
    EdhNamedValue _     !termVal -> sliceNum termVal exit'

    !badIdxNum -> edhValueRepr ets badIdxNum $ \ !badIdxNumRepr ->
      exit'
        $  Left
        $  "Bad index number of "
        <> T.pack (edhTypeNameOf badIdxNum)
        <> ": "
        <> badIdxNumRepr


edhRegulateSlice
  :: EdhThreadState
  -> Int
  -> (Maybe Int, Maybe Int, Maybe Int)
  -> ((Int, Int, Int) -> STM ())
  -> STM ()
edhRegulateSlice !ets !len (!start, !stop, !step) !exit = case step of
  Nothing -> case start of
    Nothing -> case stop of
      Nothing     -> exit (0, len, 1)

      -- (Any:iStop:Any)
      Just !iStop -> if iStop < 0
        then
          let iStop' = len + iStop
          in  if iStop' < 0
                then
                  throwEdh ets UsageError
                  $  "Stop index out of bounds: "
                  <> T.pack (show iStop)
                  <> " vs "
                  <> T.pack (show len)
                else exit (0, iStop', 1)
        else if iStop > len
          then
            throwEdh ets EvalError
            $  "Stop index out of bounds: "
            <> T.pack (show iStop)
            <> " vs "
            <> T.pack (show len)
          else exit (0, iStop, 1)

    Just !iStart -> case stop of

      -- (iStart:Any:Any)
      Nothing -> if iStart < 0
        then
          let iStart' = len + iStart
          in  if iStart' < 0
                then
                  throwEdh ets UsageError
                  $  "Start index out of bounds: "
                  <> T.pack (show iStart)
                  <> " vs "
                  <> T.pack (show len)
                else exit (iStart', len, 1)
        else if iStart > len
          then
            throwEdh ets UsageError
            $  "Start index out of bounds: "
            <> T.pack (show iStart)
            <> " vs "
            <> T.pack (show len)
          else exit (iStart, len, 1)

      -- (iStart:iStop:Any)
      Just !iStop -> do
        let !iStart' = if iStart < 0 then len + iStart else iStart
            !iStop'  = if iStop < 0 then len + iStop else iStop
        if iStart' < 0
          then
            throwEdh ets UsageError
            $  "Start index out of bounds: "
            <> T.pack (show iStart)
            <> " vs "
            <> T.pack (show len)
          else if iStop' < 0
            then
              throwEdh ets EvalError
              $  "Stop index out of bounds: "
              <> T.pack (show iStop)
              <> " vs "
              <> T.pack (show len)
            else if iStart' <= iStop'
              then
                (if iStop' > len
                  then
                    throwEdh ets EvalError
                    $  "Stop index out of bounds: "
                    <> T.pack (show iStop)
                    <> " vs "
                    <> T.pack (show len)
                  else if iStart' >= len
                    then
                      throwEdh ets UsageError
                      $  "Start index out of bounds: "
                      <> T.pack (show iStart)
                      <> " vs "
                      <> T.pack (show len)
                    else exit (iStart', iStop', 1)
                )
              else
                (if iStop' >= len
                  then
                    throwEdh ets EvalError
                    $  "Stop index out of bounds: "
                    <> T.pack (show iStop)
                    <> " vs "
                    <> T.pack (show len)
                  else if iStart' > len
                    then
                      throwEdh ets UsageError
                      $  "Start index out of bounds: "
                      <> T.pack (show iStart)
                      <> " vs "
                      <> T.pack (show len)
                    else exit (iStart', iStop', -1)
                )

  Just !iStep -> if iStep == 0
    then throwEdh ets UsageError "Step can not be zero in slice"
    else if iStep < 0
      then
        (case start of
          Nothing -> case stop of

            -- (Any:Any: -n)
            Nothing     -> exit (len - 1, -1, iStep)

            -- (Any:iStop: -n)
            Just !iStop -> if iStop == -1
              then exit (len - 1, -1, iStep)
              else do
                let !iStop' = if iStop < 0 then len + iStop else iStop
                if iStop' < -1 || iStop' >= len - 1
                  then
                    throwEdh ets EvalError
                    $  "Backward stop index out of bounds: "
                    <> T.pack (show iStop)
                    <> " vs "
                    <> T.pack (show len)
                  else exit (len - 1, iStop', iStep)

          Just !iStart -> case stop of

            -- (iStart:Any: -n)
            Nothing -> do
              let !iStart' = if iStart < 0 then len + iStart else iStart
              if iStart' < 0 || iStart' >= len
                then
                  throwEdh ets UsageError
                  $  "Backward start index out of bounds: "
                  <> T.pack (show iStart)
                  <> " vs "
                  <> T.pack (show len)
                else exit (iStart', -1, iStep)

            -- (iStart:iStop: -n)
            Just !iStop -> do
              let !iStart' = if iStart < 0 then len + iStart else iStart
              if iStart' < 0 || iStart' >= len
                then
                  throwEdh ets UsageError
                  $  "Backward start index out of bounds: "
                  <> T.pack (show iStart)
                  <> " vs "
                  <> T.pack (show len)
                else if iStop == -1
                  then exit (iStart', -1, iStep)
                  else do
                    let !iStop' = if iStop < 0 then len + iStop else iStop
                    if iStop' < -1 || iStop >= len - 1
                      then
                        throwEdh ets EvalError
                        $  "Backward stop index out of bounds: "
                        <> T.pack (show iStop)
                        <> " vs "
                        <> T.pack (show len)
                      else if iStart' < iStop'
                        then
                          throwEdh ets EvalError
                          $  "Can not step backward from "
                          <> T.pack (show iStart)
                          <> " to "
                          <> T.pack (show iStop)
                        else exit (iStart', iStop', iStep)
        )
      else -- iStep > 0
        (case start of
          Nothing -> case stop of

            -- (Any:Any:n)
            Nothing     -> exit (0, len, iStep)

            -- (Any:iStop:n)
            Just !iStop -> do
              let !iStop' = if iStop < 0 then len + iStop else iStop
              if iStop' < 0 || iStop' > len
                then
                  throwEdh ets EvalError
                  $  "Stop index out of bounds: "
                  <> T.pack (show iStop)
                  <> " vs "
                  <> T.pack (show len)
                else exit (0, iStop', iStep)

          Just !iStart -> case stop of

            -- (iStart:Any:n)
            Nothing -> do
              let !iStart' = if iStart < 0 then len + iStart else iStart
              if iStart' < 0 || iStart' >= len
                then
                  throwEdh ets UsageError
                  $  "Start index out of bounds: "
                  <> T.pack (show iStart)
                  <> " vs "
                  <> T.pack (show len)
                else exit (iStart', len, iStep)

            -- (iStart:iStop:n)
            Just !iStop -> do
              let !iStart' = if iStart < 0 then len + iStart else iStart
              let !iStop'  = if iStop < 0 then len + iStop else iStop
              if iStart' > iStop'
                then
                  throwEdh ets EvalError
                  $  "Can not step from "
                  <> T.pack (show iStart)
                  <> " to "
                  <> T.pack (show iStop)
                else exit (iStart', iStop', iStep)
        )


edhRegulateIndex :: EdhThreadState -> Int -> Int -> (Int -> STM ()) -> STM ()
edhRegulateIndex !ets !len !idx !exit =
  let !posIdx = if idx < 0  -- Python style negative index
        then idx + len
        else idx
  in  if posIdx < 0 || posIdx >= len
        then
          throwEdh ets EvalError
          $  "Index out of bounds: "
          <> T.pack (show idx)
          <> " vs "
          <> T.pack (show len)
        else exit posIdx

