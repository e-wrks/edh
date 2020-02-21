{-# LANGUAGE RecordWildCards #-}

module Language.Edh.Details.Evaluate where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Control.Concurrent.STM

import           Data.Maybe
import qualified Data.ByteString               as B
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Text.Encoding
import           Data.Text.Encoding.Error
import qualified Data.Map.Strict               as Map
import           Data.List.NonEmpty             ( NonEmpty(..)
                                                , (<|)
                                                )
import qualified Data.List.NonEmpty            as NE

import           Text.Megaparsec

import           Language.Edh.Control
import           Language.Edh.Parser
import           Language.Edh.Event
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.PkgMan
import           Language.Edh.Details.Utils


deParen :: Expr -> Expr
deParen x = case x of
  ParenExpr x' -> deParen x'
  _            -> x

deBlock :: StmtSrc -> [StmtSrc]
deBlock stmt = case stmt of
  (StmtSrc (_, ExprStmt (BlockExpr stmts'))) -> stmts'
  _ -> [stmt]


evalStmt :: StmtSrc -> EdhProcExit -> EdhProg (STM ())
evalStmt ss@(StmtSrc (_, !stmt)) !exit =
  local (\pgs -> pgs { edh'context = (edh'context pgs) { contextStmt = ss } })
    $ evalStmt' stmt exit


evalBlock :: [StmtSrc] -> EdhProcExit -> EdhProg (STM ())
evalBlock []    !exit = exitEdhProc exit nil
evalBlock [!ss] !exit = evalStmt ss $ \OriginalValue {..} ->
  case valueFromOrigin of
    -- last branch does match
    (EdhCaseClose !val) -> exitEdhProc exit val
    -- explicit `fallthrough` at end of this block, cascade to outer block
    EdhFallthrough      -> exitEdhProc exit EdhFallthrough
    -- ctrl to be propagated outwards
    EdhBreak            -> exitEdhProc exit EdhBreak
    EdhContinue         -> exitEdhProc exit EdhContinue
    (EdhReturn !val)    -> exitEdhProc exit (EdhReturn val)
    -- yield should have been handled by 'evalExpr'
    (EdhYield  _   )    -> throwEdh EvalError "bug yield reached block"
    -- last stmt no special branching result, propagate as is
    _                   -> exitEdhProc exit valueFromOrigin
evalBlock (ss : rest) !exit = evalStmt ss $ \OriginalValue {..} ->
  case valueFromOrigin of
    -- this branch matches without fallthrough, done this block
    (EdhCaseClose !val) -> exitEdhProc exit val
    -- should fallthrough to next branch (or stmt)
    EdhFallthrough      -> evalBlock rest exit
    -- ctrl to be propagated outwards
    EdhBreak            -> exitEdhProc exit EdhBreak
    EdhContinue         -> exitEdhProc exit EdhContinue
    (EdhReturn !val)    -> exitEdhProc exit (EdhReturn val)
    -- yield should have been handled by 'evalExpr'
    (EdhYield  _   )    -> throwEdh EvalError "bug yield reached block"
    -- no special branching result, continue this block
    _                   -> evalBlock rest exit


-- | a left-to-right expr list eval'er, returning a tuple
evalExprs :: [Expr] -> EdhProcExit -> EdhProg (STM ())
-- here 'EdhTuple' is used for intermediate tag,
-- not returning actual tuple values as in Edh.
evalExprs []       !exit = exitEdhProc exit (EdhTuple [])
evalExprs (x : xs) !exit = evalExpr x $ \OriginalValue {..} ->
  evalExprs xs $ \(OriginalValue !tv _ _) -> case tv of
    EdhTuple l -> exitEdhProc exit (EdhTuple (valueFromOrigin : l))
    _          -> error "bug"


evalStmt' :: Stmt -> EdhProcExit -> EdhProg (STM ())
evalStmt' !stmt !exit = do
  !pgs <- ask
  let !ctx                   = edh'context pgs
      !world                 = contextWorld ctx
      !call'stack            = callStack ctx
      (StmtSrc (!srcPos, _)) = contextStmt ctx
      !scope                 = contextScope ctx
  case stmt of

    ExprStmt expr -> evalExpr expr exit

    LetStmt argsRcvr argsSndr ->
      -- ensure args sending and receiving happens within a same tx
      -- for atomicity of the let statement
      local (const pgs { edh'in'tx = True })
        $ packEdhArgs pgs argsSndr
        $ \pk -> recvEdhArgs ctx argsRcvr pk $ \rcvd'ent -> contEdhSTM $ do
          -- overwrite current scope entity with attributes from the
          -- received entity
            um <- readTVar rcvd'ent
            modifyTVar' (scopeEntity scope) $ \em -> Map.union um em
            -- let statement evaluates to nil always, with previous tx
            -- state restored
            exitEdhSTM pgs exit nil

    BreakStmt       -> exitEdhProc exit EdhBreak
    ContinueStmt    -> exitEdhProc exit EdhContinue
    FallthroughStmt -> exitEdhProc exit EdhFallthrough

    ReturnStmt expr -> evalExpr expr
      $ \OriginalValue {..} -> exitEdhProc exit (EdhReturn valueFromOrigin)


    AtoIsoStmt expr ->
      contEdhSTM
        $ runEdhProg pgs { edh'in'tx = True } -- ensure in'tx state
        $ evalExpr expr
        $ \OriginalValue {..} -> -- restore original tx state
            contEdhSTM $ exitEdhSTM pgs exit valueFromOrigin


    GoStmt expr -> case expr of

      CaseExpr tgtExpr branchesStmt ->
        evalExpr tgtExpr $ \OriginalValue {..} ->
          forkEdh exit
            $ contEdhSTM
            $ runEdhProg pgs
                { edh'context = ctx { contextMatch = valueFromOrigin }
                } -- eval the branch(es) expr with the case target being
                  -- the 'contextMatch'
            $ evalBlock (deBlock branchesStmt) edhNop

      (CallExpr procExpr argsSndr) ->
        evalExpr procExpr $ \(OriginalValue !callee'val _ !callee'that) ->
          contEdhSTM
            $ edhMakeCall pgs callee'val callee'that argsSndr
            $ \mkCall -> runEdhProg pgs $ forkEdh exit (mkCall edhNop)

      (ForExpr argsRcvr iterExpr doExpr) ->
        contEdhSTM
          $ edhForLoop pgs argsRcvr iterExpr doExpr (const $ return ())
          $ \runLoop -> runEdhProg pgs $ forkEdh exit (runLoop edhNop)

      _ -> forkEdh exit $ evalExpr expr edhNop

    DeferStmt expr -> do
      let schedDefered :: EdhProgState -> EdhProg (STM ()) -> STM ()
          schedDefered pgs' prog = do
            modifyTVar' (edh'defers pgs) ((pgs', prog) :)
            exitEdhSTM pgs exit nil
      case expr of

        CaseExpr tgtExpr branchesStmt ->
          evalExpr tgtExpr $ \OriginalValue {..} ->
            contEdhSTM
              $ schedDefered pgs
                  { edh'context = ctx { contextMatch = valueFromOrigin }
                  } -- eval the branch(es) expr with the case target being
                    -- the 'contextMatch'
              $ evalBlock (deBlock branchesStmt) edhNop

        (CallExpr procExpr argsSndr) ->
          evalExpr procExpr $ \(OriginalValue callee'val _ callee'that) ->
            contEdhSTM
              $ edhMakeCall pgs callee'val callee'that argsSndr
              $ \mkCall -> schedDefered pgs (mkCall edhNop)

        (ForExpr argsRcvr iterExpr doExpr) ->
          contEdhSTM
            $ edhForLoop pgs argsRcvr iterExpr doExpr (const $ return ())
            $ \runLoop -> schedDefered pgs (runLoop edhNop)

        _ -> contEdhSTM $ schedDefered pgs $ evalExpr expr edhNop


    ReactorStmt sinkExpr argsRcvr reactionStmt ->
      evalExpr sinkExpr $ \(OriginalValue !val _ _) -> case val of
        (EdhSink sink) -> contEdhSTM $ do
          (reactorChan, _) <- subscribeEvents sink
          modifyTVar' (edh'reactors pgs)
                      ((reactorChan, pgs, argsRcvr, reactionStmt) :)
          exitEdhSTM pgs exit nil
        _ ->
          throwEdh EvalError
            $  "Can only reacting to an event sink, not a "
            <> T.pack (show $ edhTypeOf val)
            <> ": "
            <> T.pack (show val)


    -- TODO impl. this
    -- TryStmt trunkStmt catchesList finallyStmt -> undefined
    -- ThrowStmt excExpr                         -> undefined


    WhileStmt cndExpr bodyStmt -> do
      let
        !stmts = deBlock bodyStmt
        doWhile :: EdhProg (STM ())
        doWhile = evalExpr cndExpr $ \(OriginalValue !cndVal _ _) ->
          case cndVal of
            (EdhBool True) ->
              evalBlock stmts $ \(OriginalValue !blkVal _ _) -> case blkVal of
                -- early stop of procedure
                EdhReturn rtnVal   -> exitEdhProc exit rtnVal
                -- break while loop
                EdhBreak           -> exitEdhProc exit nil
                -- treat as break here, TODO judge this decision
                EdhFallthrough     -> exitEdhProc exit nil
                -- treat as continue here, TODO judge this decision
                EdhCaseClose ccVal -> exitEdhProc exit ccVal
                -- continue while loop
                _                  -> doWhile
            (EdhBool False) -> exitEdhProc exit nil
            EdhNil          -> exitEdhProc exit nil
            _ ->
              throwEdh EvalError
                $  "Invalid condition value for while: "
                <> T.pack (show $ edhTypeOf cndVal)
                <> ": "
                <> T.pack (show cndVal)
      doWhile

    ExtendsStmt superExpr ->
      evalExpr superExpr $ \(OriginalValue !superVal _ _) -> case superVal of
        (EdhObject superObj) ->
          let
            !this = thisObject scope
            !key  = AttrByName "<-^"
            doExtend :: STM ()
            doExtend = do
              modifyTVar' (objSupers this) (superObj :)
              exitEdhSTM pgs exit nil
            noMagic :: EdhProg (STM ())
            noMagic = contEdhSTM $ resolveEdhObjAttr superObj key >>= \case
              Nothing                            -> doExtend
              Just (OriginalValue !magicMth _ _) -> withMagicMethod magicMth
            withMagicMethod :: EdhValue -> STM ()
            withMagicMethod magicMth = do
              scopeObj <- mkScopeWrapper
                (contextWorld ctx)
                scope { scopeEntity = objEntity this }
              edhMakeCall pgs
                          magicMth
                          this
                          [SendPosArg (GodSendExpr $ EdhObject scopeObj)]
                $ \mkCall ->
                    runEdhProg pgs $ mkCall $ const $ contEdhSTM doExtend
          in
            getEdhAttrWithMagic (AttrByName "!<-") superObj key noMagic
              $ \(OriginalValue !magicMth _ _) ->
                  contEdhSTM $ withMagicMethod magicMth
        _ ->
          throwEdh EvalError
            $  "Can only extends an object, not "
            <> T.pack (show $ edhTypeOf superVal)
            <> ": "
            <> T.pack (show superVal)

    ClassStmt pd@(ProcDecl name _ _) -> contEdhSTM $ do
      let
        !cls =
          EdhClass $ Class { classLexiStack = call'stack, classProcedure = pd }
      when (name /= "_") $ modifyTVar' (scopeEntity scope) $ Map.insert
        (AttrByName name)
        cls
      exitEdhSTM pgs exit cls

    MethodStmt pd@(ProcDecl name _ _) -> contEdhSTM $ do
      let
        mth = EdhMethod
          $ Method { methodLexiStack = call'stack, methodProcedure = pd }
      when (name /= "_") $ modifyTVar' (scopeEntity scope) $ Map.insert
        (AttrByName name)
        mth
      exitEdhSTM pgs exit mth

    GeneratorStmt pd@(ProcDecl name _ _) -> contEdhSTM $ do
      let gdf = EdhGenrDef $ GenrDef { generatorLexiStack = call'stack
                                     , generatorProcedure = pd
                                     }
      when (name /= "_") $ modifyTVar' (scopeEntity scope) $ Map.insert
        (AttrByName name)
        gdf
      exitEdhSTM pgs exit gdf

    InterpreterStmt pd@(ProcDecl name _ _) -> contEdhSTM $ do
      let mth = EdhInterpreter $ Interpreter
            { interpreterLexiStack = call'stack
            , interpreterProcedure = pd
            }
      when (name /= "_") $ modifyTVar' (scopeEntity scope) $ Map.insert
        (AttrByName name)
        mth
      exitEdhSTM pgs exit mth

    OpDeclStmt opSym opPrec opProc@(ProcDecl _ _ (StmtSrc (_, body'stmt))) ->
      case body'stmt of
        -- support re-declaring an existing operator to another name,
        -- with possibly a different precedence
        ExprStmt (AttrExpr (DirectRef (NamedAttr !origOpSym))) ->
          contEdhSTM $ do
            origOp <- lookupEdhCtxAttr scope (AttrByName origOpSym) >>= \case
              Nothing ->
                throwEdhSTM pgs EvalError
                  $  "Original operator ("
                  <> origOpSym
                  <> ") not in scope"
              Just (EdhHostOper _ !hp) -> return $ EdhHostOper opPrec hp
              Just surfOper@(EdhOperator _) -> return surfOper
              Just val ->
                throwEdhSTM pgs EvalError
                  $  "Can not re-declare a "
                  <> T.pack (show $ edhTypeOf val)
                  <> ": "
                  <> T.pack (show val)
                  <> " as an operator"
            modifyTVar' (scopeEntity scope)
              $ Map.insert (AttrByName opSym) origOp
            exitEdhSTM pgs exit origOp
        _ -> contEdhSTM $ do
          validateOperDecl pgs opProc
          let op = EdhOperator $ Operator { operatorLexiStack   = call'stack
                                          , operatorProcedure   = opProc
                                          , operatorPredecessor = Nothing
                                          , operatorPrecedence  = opPrec
                                          }
          modifyTVar' (scopeEntity scope)
            $ \em -> Map.insert (AttrByName opSym) op em
          exitEdhSTM pgs exit op

    OpOvrdStmt opSym opProc opPrec -> contEdhSTM $ do
      validateOperDecl pgs opProc
      let findPredecessor :: STM (Maybe EdhValue)
          findPredecessor = lookupEdhCtxAttr scope (AttrByName opSym) >>= \case
            Nothing -> -- do
              -- (EdhRuntime logger _) <- readTMVar $ worldRuntime world
              -- logger 30 (Just $ sourcePosPretty srcPos)
              --   $ ArgsPack
              --       [EdhString "overriding an unavailable operator"]
              --       Map.empty
              return Nothing
            Just hostOper@(EdhHostOper _ _) -> return $ Just hostOper
            Just surfOper@(EdhOperator _  ) -> return $ Just surfOper
            Just opVal                      -> do
              (EdhRuntime logger _) <- readTMVar $ worldRuntime world
              logger 30 (Just $ sourcePosPretty srcPos) $ ArgsPack
                [ EdhString
                  $  "overriding an invalid operator "
                  <> T.pack (show $ edhTypeOf opVal)
                  <> ": "
                  <> T.pack (show opVal)
                ]
                Map.empty
              return Nothing
      predecessor <- findPredecessor
      let op = EdhOperator $ Operator { operatorLexiStack   = call'stack
                                      , operatorProcedure   = opProc
                                      , operatorPredecessor = predecessor
                                      , operatorPrecedence  = opPrec
                                      }
      modifyTVar' (scopeEntity scope)
        $ \em -> Map.insert (AttrByName opSym) op em
      exitEdhSTM pgs exit op

    ImportStmt argsRcvr srcExpr -> case srcExpr of
      LitExpr (StringLiteral importSpec) ->
        -- import from specified path
        importEdhModule argsRcvr importSpec exit
      _ -> evalExpr srcExpr $ \(OriginalValue !srcVal _ _) -> case srcVal of
        EdhObject fromObj ->
          -- import from an object
          importFromObject argsRcvr fromObj exit
        _ ->
          -- todo support more sources of import ?
          throwEdh EvalError
            $  "Don't know how to import from a "
            <> T.pack (show $ edhTypeOf srcVal)
            <> ": "
            <> T.pack (show srcVal)

    VoidStmt -> exitEdhProc exit nil

    _ -> throwEdh EvalError $ "Eval not yet impl for: " <> T.pack (show stmt)


importFromObject :: ArgsReceiver -> Object -> EdhProcExit -> EdhProg (STM ())
importFromObject !argsRcvr !fromObj !exit = do
  pgs <- ask
  let !ctx   = edh'context pgs
      !scope = contextScope ctx
  contEdhSTM $ do
    emImp <- readTVar $ objEntity fromObj
    let !artsPk = ArgsPack [] $ Map.fromAscList $ catMaybes
          [ (case k of
-- only attributes with a name not started with `_` are importable,
-- and all symbol values are not importable however named
              AttrByName attrName | not (T.isPrefixOf "_" attrName) -> case v of
                EdhSymbol _ -> Nothing
                _           -> Just (attrName, v)
-- symbolic attributes are effective stripped off, this is desirable so that
-- symbolic attributes are not importable, thus private to a module/object
              _ -> Nothing
            )
          | (k, v) <- Map.toAscList emImp
          ]
    runEdhProg pgs $ recvEdhArgs ctx argsRcvr artsPk $ \ent -> contEdhSTM $ do
      em <- readTVar ent
      modifyTVar' (scopeEntity scope) $ Map.union em
      exitEdhSTM pgs exit (EdhObject fromObj)

importEdhModule :: ArgsReceiver -> Text -> EdhProcExit -> EdhProg (STM ())
importEdhModule !argsRcvr !impSpec !exit = do
  pgs <- ask
  let !ctx   = edh'context pgs
      !world = contextWorld ctx
      !scope = contextScope ctx
  if edh'in'tx pgs
    then throwEdh EvalError "You don't import from within a transaction"
    else contEdhSTM $ lookupEdhCtxAttr scope (AttrByName "__file__") >>= \case
      Just (EdhString fromModuPath) -> do
        (nomPath, moduFile) <- locateEdhModule
          pgs
          (edhPkgPathFrom $ T.unpack fromModuPath)
          (T.unpack impSpec)
        let !moduId = T.pack nomPath
        moduMap <- takeTMVar (worldModules world)
        case Map.lookup moduId moduMap of
          Just !moduSlot -> do
            -- put back immediately
            putTMVar (worldModules world) moduMap
            -- blocking wait the target module loaded, then do import
            readTMVar moduSlot >>= \case
              -- TODO GHC should be able to detect cyclic imports as 
              --      deadlock, find ways to report that more friendly
              EdhObject modu ->
                runEdhProg pgs $ importFromObject argsRcvr modu exit
              importError -> -- the first importer failed loading it,
                -- replicate the error in this thread
                throwEdhSTM pgs EvalError $ edhValueStr importError
          Nothing -> do  -- we are the first importer
            -- allocate an empty slot
            moduSlot <- newEmptyTMVar
            -- put it for global visibility
            putTMVar (worldModules world) $ Map.insert moduId moduSlot moduMap
            catchSTM
                ( loadModule pgs moduSlot moduId moduFile
                $ \(OriginalValue !result _ _) -> case result of
                    (EdhObject modu) ->
                      -- do the import after module successfully loaded
                      importFromObject argsRcvr modu exit
                    _ -> error "bug"
                )
              $ \(e :: SomeException) -> do
                  -- cleanup on loading error
                  let errStr = T.pack (show e)
                  void $ tryPutTMVar moduSlot $ EdhString errStr
                  moduMap' <- takeTMVar (worldModules world)
                  case Map.lookup moduId moduMap' of
                    Just moduSlot' -> if moduSlot' == moduSlot
                      then putTMVar (worldModules world)
                        $ Map.delete moduId moduMap'
                      else putTMVar (worldModules world) moduMap'
                    _ -> putTMVar (worldModules world) moduMap'
                  throwSTM e
      _ -> error "bug: no valid `__file__` in context"

loadModule
  :: EdhProgState
  -> TMVar EdhValue
  -> ModuleId
  -> FilePath
  -> EdhProcExit
  -> STM ()
loadModule !pgs !moduSlot !moduId !moduFile !exit = if edh'in'tx pgs
  then throwEdhSTM pgs
                   EvalError
                   "You don't load a module from within a transaction"
  else
    unsafeIOToSTM (streamDecodeUtf8With lenientDecode <$> B.readFile moduFile)
      >>= \case
            Some moduSource _ _ -> do
              let !ctx   = edh'context pgs
                  !world = contextWorld ctx
                  !wops  = worldOperators world
              -- serialize parsing against 'worldOperators'
              opPD <- takeTMVar wops
              flip
                  catchSTM
                  (\(e :: SomeException) -> tryPutTMVar wops opPD >> throwSTM e)
                $ do
                    -- parse module source
                    let
                      (pr, opPD') = runState
                        (runParserT parseProgram moduFile moduSource)
                        opPD
                    case pr of
                      Left  !err   -> throwSTM $ EdhParseError err
                      Right !stmts -> do
                        -- release world lock as soon as parsing done successfuly
                        putTMVar wops opPD'
                        -- prepare the module meta data
                        !moduEntity <- newTVar $ Map.fromList
                          [ (AttrByName "__name__", EdhString moduId)
                          , (AttrByName "__file__", EdhString $ T.pack moduFile)
                          ]
                        !moduSupers <- newTVar []
                        let !modu = Object { objEntity = moduEntity
                                           , objClass  = moduleClass world
                                           , objSupers = moduSupers
                                           }
                        moduCtx <- moduleContext world modu
                        -- run statements from the module with its own context
                        runEdhProg pgs { edh'context = moduCtx }
                          $ evalBlock stmts
                          $ \_ -> contEdhSTM $ do
                              -- arm the successfully loaded module
                              putTMVar moduSlot $ EdhObject modu
                              -- switch back to module importer's scope and continue
                              exitEdhSTM pgs exit (EdhObject modu)


moduleContext :: EdhWorld -> Object -> STM Context
moduleContext !world !modu = moduleInfo modu >>= \(moduName, moduFile) ->
  let !moduScope = Scope
        (objEntity modu)
        modu
        modu
        (NE.toList rootScope)
        (classProcedure $ moduleClass world)
          { procedure'name = moduName
          , procedure'body = StmtSrc
                               ( SourcePos { sourceName   = T.unpack moduFile
                                           , sourceLine   = mkPos 1
                                           , sourceColumn = mkPos 1
                                           }
                               , VoidStmt
                               )
          }
  in  return Context { contextWorld    = world
                     , callStack       = moduScope <| rootScope
                     , generatorCaller = Nothing
                     , contextMatch    = true
                     , contextStmt     = voidStatement
                     }
  where !rootScope = classLexiStack $ moduleClass world

moduleInfo :: Object -> STM (Text, Text)
moduleInfo !modu = do
  em <- readTVar $ objEntity modu
  case flip Map.lookup em . AttrByName <$> ["__name__", "__file__"] of
    [Just (EdhString moduName), Just (EdhString moduFile)] ->
      return (moduName, moduFile)
    _ -> error "bug: module has no valid __name__ and/or __file__"

voidStatement :: StmtSrc
voidStatement = StmtSrc
  ( SourcePos { sourceName   = "<Genesis>"
              , sourceLine   = mkPos 1
              , sourceColumn = mkPos 1
              }
  , VoidStmt
  )
{-# INLINE voidStatement #-}


evalExpr :: Expr -> EdhProcExit -> EdhProg (STM ())
evalExpr expr exit = do
  !pgs <- ask
  let !ctx                   = edh'context pgs
      !world                 = contextWorld ctx
      !genr'caller           = generatorCaller ctx
      (StmtSrc (!srcPos, _)) = contextStmt ctx
      !scope                 = contextScope ctx
  case expr of
    GodSendExpr !val -> exitEdhProc exit val

    LitExpr     lit  -> case lit of
      DecLiteral    v -> exitEdhProc exit (EdhDecimal v)
      StringLiteral v -> exitEdhProc exit (EdhString v)
      BoolLiteral   v -> exitEdhProc exit (EdhBool v)
      NilLiteral      -> exitEdhProc exit nil
      TypeLiteral v   -> exitEdhProc exit (EdhType v)

      SinkCtor        -> contEdhSTM $ do
        es <- newEventSink
        exitEdhSTM pgs exit (EdhSink es)

    PrefixExpr prefix expr' -> case prefix of
      PrefixPlus  -> evalExpr expr' exit
      PrefixMinus -> evalExpr expr' $ \(OriginalValue !val _ _) -> case val of
        (EdhDecimal v) -> exitEdhProc exit (EdhDecimal (-v))
        _ ->
          throwEdh EvalError
            $  "Can not negate a "
            <> T.pack (show $ edhTypeOf val)
            <> ": "
            <> T.pack (show val)
            <> " ❌"
      Not -> evalExpr expr' $ \(OriginalValue !val _ _) -> case val of
        (EdhBool v) -> exitEdhProc exit (EdhBool $ not v)
        _ ->
          throwEdh EvalError
            $  "Expect bool but got a "
            <> T.pack (show $ edhTypeOf val)
            <> ": "
            <> T.pack (show val)
            <> " ❌"
      Guard -> contEdhSTM $ do
        (EdhRuntime logger _) <- readTMVar $ worldRuntime world
        logger
          30
          (Just $ sourcePosPretty srcPos)
          (ArgsPack [EdhString $ "Standalone guard treated as plain value."]
                    Map.empty
          )
        runEdhProg pgs $ evalExpr expr' exit

    IfExpr cond cseq alt -> evalExpr cond $ \(OriginalValue !val _ _) ->
      case val of
        (EdhBool True ) -> evalStmt cseq exit
        (EdhBool False) -> case alt of
          Just elseClause -> evalStmt elseClause exit
          _               -> exitEdhProc exit nil
        _ ->
          -- we are so strongly typed
          throwEdh EvalError
            $  "Expecting a boolean value but got a "
            <> T.pack (show $ edhTypeOf val)
            <> ": "
            <> T.pack (show val)
            <> " ❌"

    DictExpr xs -> -- make sure dict k:v pairs are evaluated in same tx
      local (\s -> s { edh'in'tx = True })
        $ evalExprs xs
        $ \(OriginalValue !tv _ _) -> case tv of
            EdhTuple l -> contEdhSTM $ do
              dpl <- forM l $ \case
                EdhPair kVal vVal -> (, vVal) <$> case kVal of
                  EdhString  k -> return $ ItemByStr k
                  EdhSymbol  k -> return $ ItemBySym k
                  EdhDecimal k -> return $ ItemByNum k
                  EdhBool    k -> return $ ItemByBool k
                  EdhType    k -> return $ ItemByType k
                  EdhClass   k -> return $ ItemByClass k
                  k ->
                    throwEdhSTM pgs EvalError
                      $  "Invalid dict key "
                      <> T.pack (show $ edhTypeOf k)
                      <> ": "
                      <> T.pack (show k)
                      <> " ❌"
                pv ->
                  throwEdhSTM pgs EvalError
                    $  "Invalid dict entry "
                    <> T.pack (show $ edhTypeOf pv)
                    <> ": "
                    <> T.pack (show pv)
                    <> " ❌"
              ds <- newTVar $ Map.fromList dpl
              exitEdhSTM pgs exit (EdhDict (Dict ds))
            _ -> error "bug"

    ListExpr xs -> -- make sure list values are evaluated in same tx
      local (\s -> s { edh'in'tx = True })
        $ evalExprs xs
        $ \(OriginalValue !tv _ _) -> case tv of
            EdhTuple l -> contEdhSTM $ do
              ll <- List <$> newTVar l
              exitEdhSTM pgs exit (EdhList ll)
            _ -> error "bug"

    TupleExpr xs -> -- make sure tuple values are evaluated in same tx
      local (\s -> s { edh'in'tx = True })
        $ evalExprs xs
        $ \(OriginalValue !tv _ _) -> case tv of
            EdhTuple l -> exitEdhProc exit (EdhTuple l)
            _          -> error "bug"

    ParenExpr x -> evalExpr x exit

    BlockExpr stmts ->
      -- eval the block with `true` being the 'contextMatch'
      local (const pgs { edh'context = ctx { contextMatch = true } })
        $ evalBlock stmts
        -- restore program state after block done
        $ \(OriginalValue !blkResult _ _) ->
            local (const pgs) $ exitEdhProc exit blkResult

    CaseExpr tgtExpr branchesStmt ->
      evalExpr tgtExpr $ \(OriginalValue !tgtVal _ _) ->
        -- eval the branch(es) expr with the case target being the 'contextMatch'
        local (const pgs { edh'context = ctx { contextMatch = tgtVal } })
          $ evalBlock (deBlock branchesStmt)
          -- restore program state after block done
          $ \(OriginalValue !blkResult _ _) ->
              local (const pgs) $ exitEdhProc exit blkResult


    -- yield stmt evals to the value of caller's `do` expression
    YieldExpr yieldExpr ->
      evalExpr yieldExpr $ \(OriginalValue !yieldResult _ _) ->
        case genr'caller of
          Nothing -> throwEdh EvalError "Unexpected yield"
          Just (pgsGenrCaller, yieldTo) ->
            contEdhSTM
              $ runEdhProg pgsGenrCaller
              $ yieldTo yieldResult
              $ \doResult -> exitEdhSTM pgs exit doResult

    ForExpr argsRcvr iterExpr doExpr ->
      contEdhSTM
        $ edhForLoop pgs argsRcvr iterExpr doExpr (const $ return ())
        $ \runLoop -> runEdhProg pgs (runLoop exit)


    AttrExpr addr -> case addr of
      ThisRef          -> exitEdhProc exit (EdhObject $ thisObject scope)
      ThatRef          -> exitEdhProc exit (EdhObject $ thatObject scope)
      SuperRef -> throwEdh EvalError "Can not address a single super alone"
      DirectRef !addr' -> contEdhSTM $ do
        !key <- resolveAddr pgs addr'
        resolveEdhCtxAttr scope key >>= \case
          Nothing ->
            throwEdhSTM pgs EvalError $ "Not in scope: " <> T.pack (show addr')
          Just !originVal -> exitEdhSTM' pgs exit originVal
      IndirectRef !tgtExpr !addr' -> contEdhSTM $ do
        key <- resolveAddr pgs addr'
        runEdhProg pgs $ getEdhAttr
          tgtExpr
          key
          (  throwEdh EvalError
          $  "No such attribute "
          <> T.pack (show key)
          <> " from "
          <> T.pack (show tgtExpr)
          )
          exit


    IndexExpr ixExpr tgtExpr ->
      evalExpr ixExpr $ \(OriginalValue !ixVal _ _) ->
        evalExpr tgtExpr $ \(OriginalValue !tgtVal _ _) -> case tgtVal of

        -- indexing a dict
          (EdhDict (Dict d)) -> contEdhSTM $ do
            ixKey <- case ixVal of
              EdhString  s -> return $ ItemByStr s
              EdhSymbol  s -> return $ ItemBySym s
              EdhDecimal n -> return $ ItemByNum n
              EdhBool    b -> return $ ItemByBool b
              EdhType    t -> return $ ItemByType t
              EdhClass   c -> return $ ItemByClass c
              _ ->
                throwEdhSTM pgs EvalError
                  $  "Invalid dict key: "
                  <> T.pack (show $ edhTypeOf ixVal)
                  <> ": "
                  <> T.pack (show ixVal)
            ds <- readTVar d
            case Map.lookup ixKey ds of
              Nothing  -> exitEdhSTM pgs exit nil
              Just val -> exitEdhSTM pgs exit val

          -- indexing an object, by calling its ([]) method with ixVal as the single arg
          (EdhObject obj) ->
            contEdhSTM $ resolveEdhObjAttr obj (AttrByName "[]") >>= \case
              Nothing ->
                throwEdhSTM pgs EvalError $ "No ([]) method from: " <> T.pack
                  (show obj)
              Just (OriginalValue (EdhMethod (Method mth'lexi'stack mth'proc)) _ mth'that)
                -> runEdhProg pgs $ callEdhMethod (ArgsPack [ixVal] Map.empty)
                                                  mth'that
                                                  mth'lexi'stack
                                                  mth'proc
                                                  Nothing
                                                  exit
              Just (OriginalValue !badIndexer _ _) ->
                throwEdhSTM pgs EvalError
                  $  "Malformed index method ([]) on "
                  <> T.pack (show obj)
                  <> " - "
                  <> T.pack (show $ edhTypeOf badIndexer)
                  <> ": "
                  <> T.pack (show badIndexer)

          _ ->
            throwEdh EvalError
              $  "Don't know how to index "
              <> T.pack (show $ edhTypeOf tgtVal)
              <> ": "
              <> T.pack (show tgtVal)
              <> " with "
              <> T.pack (show $ edhTypeOf ixVal)
              <> ": "
              <> T.pack (show ixVal)


    CallExpr procExpr argsSndr ->
      evalExpr procExpr $ \(OriginalValue callee'val _ callee'that) ->
        contEdhSTM
          $ edhMakeCall pgs callee'val callee'that argsSndr
          $ \mkCall -> runEdhProg pgs (mkCall exit)


    InfixExpr !opSym !lhExpr !rhExpr ->
      contEdhSTM $ resolveEdhCtxAttr scope (AttrByName opSym) >>= \case
        Nothing ->
          throwEdhSTM pgs EvalError
            $  "Operator ("
            <> T.pack (show opSym)
            <> ") not in scope"
        Just (OriginalValue !opVal _ !op'that) -> case opVal of

          -- calling a host operator
          (EdhHostOper _ (HostProcedure _ !proc)) ->
            -- insert a cycle tick here, so if no tx required for the call
            -- overall, the op resolution tx stops here then the op
            -- runs in next stm transaction
            flip (exitEdhSTM' pgs) (wuji pgs)
              $ \_ -> proc [SendPosArg lhExpr, SendPosArg rhExpr] exit

          -- calling an operator
          (EdhOperator (Operator op'lexi'stack op'proc@(ProcDecl _ op'args op'body) op'pred _))
            -> case op'args of
              -- 2 pos-args - simple lh/rh value receiving operator
              (PackReceiver [RecvArg lhName Nothing Nothing, RecvArg rhName Nothing Nothing])
                -> runEdhProg pgs
                  $ evalExpr lhExpr
                  $ \(OriginalValue !lhVal _ _) ->
                      evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
                        contEdhSTM $ do
                          opEnt <-
                            newTVar
                            $  Map.fromList
                            $  [ (AttrByName lhName, lhVal)
                               , (AttrByName rhName, rhVal)
                               ]
                            ++ case op'pred of
                                -- put the overridden (predecessor) operator in the overriding
                                -- operator's scope
                                 Nothing -> []
                                 Just predProc ->
                                   [(AttrByName opSym, predProc)]
                          let !opScope = scope
                                { scopeEntity = opEnt
                                , thatObject  = op'that
                                , lexiStack   = NE.toList op'lexi'stack
                                , scopeProc   = op'proc
                                }
                              !opCtx = ctx
                                { callStack       = opScope <| callStack ctx
                                , generatorCaller = Nothing
                                , contextMatch    = true
                                , contextStmt     = voidStatement
                                }
                              !pgsOp = pgs { edh'context = opCtx }
                          runEdhProg pgsOp
                            $ evalStmt op'body
                            $ \(OriginalValue !opRtn _ _) ->
                                local (const pgs) $ case opRtn of
                                -- allow continue to be return from a operator proc,
                                -- to carry similar semantics like `NotImplemented` in Python
                                  EdhContinue -> exitEdhProc exit EdhContinue
                                  -- allow the use of `break` to early stop a operator 
                                  -- operator with nil result
                                  EdhBreak         -> exitEdhProc exit nil
                                  -- explicit return
                                  EdhReturn rtnVal -> exitEdhProc exit rtnVal
                                  -- no explicit return, assuming it returns the last
                                  -- value from operator execution
                                  _                -> exitEdhProc exit opRtn

              -- 3 pos-args - caller scope + lh/rh expr receiving operator
              (PackReceiver [RecvArg scopeName Nothing Nothing, RecvArg lhName Nothing Nothing, RecvArg rhName Nothing Nothing])
                -> do
                  scopeWrapper <- mkScopeWrapper world scope
                  opEnt        <-
                    newTVar
                    $  Map.fromList
                    $  [ (AttrByName scopeName, EdhObject scopeWrapper)
                       , (AttrByName lhName   , EdhExpr lhExpr)
                       , (AttrByName rhName   , EdhExpr rhExpr)
                       ]
                    ++ case op'pred of
                        -- put the overridden (predecessor) operator in the overriding
                        -- operator's scope
                         Nothing       -> []
                         Just predProc -> [(AttrByName opSym, predProc)]
                  let !opScope = scope { scopeEntity = opEnt
                                       , thatObject  = op'that
                                       , lexiStack   = NE.toList op'lexi'stack
                                       , scopeProc   = op'proc
                                       }
                      !opCtx = ctx { callStack       = opScope <| callStack ctx
                                   , generatorCaller = Nothing
                                   , contextMatch    = true
                                   , contextStmt     = voidStatement
                                   }
                      !pgsOp = pgs { edh'context = opCtx }
                  runEdhProg pgsOp
                    $ evalStmt op'body
                    $ \(OriginalValue !opRtn _ _) ->
                        local (const pgs) $ case opRtn of
                          -- allow continue to be return from a operator proc,
                          -- to carry similar semantics like `NotImplemented` in Python
                          EdhContinue      -> exitEdhProc exit EdhContinue
                          -- allow the use of `break` to early stop a operator 
                          -- operator with nil result
                          EdhBreak         -> exitEdhProc exit nil
                          -- explicit return
                          EdhReturn rtnVal -> exitEdhProc exit rtnVal
                          -- no explicit return, assuming it returns the last
                          -- value from operator execution
                          _                -> exitEdhProc exit opRtn

              _ ->
                throwEdhSTM pgs EvalError
                  $  "Invalid operator signature: "
                  <> T.pack (show op'args)

          _ ->
            throwEdhSTM pgs EvalError
              $  "Not callable "
              <> T.pack (show $ edhTypeOf opVal)
              <> ": "
              <> T.pack (show opVal)
              <> " expressed with: "
              <> T.pack (show expr)


    -- _ -> throwEdh EvalError $ "Eval not yet impl for: " <> T.pack (show expr)


validateOperDecl :: EdhProgState -> ProcDecl -> STM ()
validateOperDecl !pgs (ProcDecl _ !op'args _) = case op'args of
  -- 2 pos-args - simple lh/rh value receiving operator
  (PackReceiver [RecvArg _lhName Nothing Nothing, RecvArg _rhName Nothing Nothing])
    -> return ()
  -- 3 pos-args - caller scope + lh/rh expr receiving operator
  (PackReceiver [RecvArg _scopeName Nothing Nothing, RecvArg _lhName Nothing Nothing, RecvArg _rhName Nothing Nothing])
    -> return ()
  _ -> throwEdhSTM pgs EvalError "Invalid operator signature"


getEdhAttr
  :: Expr -> AttrKey -> EdhProg (STM ()) -> EdhProcExit -> EdhProg (STM ())
getEdhAttr !fromExpr !key !exitNoAttr !exit = do
  !pgs <- ask
  let scope = contextScope $ edh'context pgs
  case fromExpr of
    -- give super objects the magical power to intercept
    -- attribute access on descendant objects, via `this` ref
    AttrExpr ThisRef ->
      let !this = thisObject scope
          noMagic :: EdhProg (STM ())
          noMagic = contEdhSTM $ resolveEdhObjAttr this key >>= \case
            Nothing         -> runEdhProg pgs exitNoAttr
            Just !originVal -> exitEdhSTM' pgs exit originVal
      in  getEdhAttrWithMagic (AttrByName "@<-") this key noMagic exit
    -- no magic layer laid over access via `that` ref
    AttrExpr ThatRef ->
      let !that = thatObject scope
      in  contEdhSTM $ resolveEdhObjAttr that key >>= \case
            Nothing         -> runEdhProg pgs exitNoAttr
            Just !originVal -> exitEdhSTM' pgs exit originVal
    -- give super objects of an super object the metamagical power to
    -- intercept attribute access on super object, via `super` ref
    AttrExpr SuperRef ->
      let !this = thisObject scope
          noMagic :: EdhProg (STM ())
          noMagic = contEdhSTM $ resolveEdhSuperAttr this key >>= \case
            Nothing         -> runEdhProg pgs exitNoAttr
            Just !originVal -> exitEdhSTM' pgs exit originVal
          getFromSupers :: [Object] -> EdhProg (STM ())
          getFromSupers []                   = noMagic
          getFromSupers (super : restSupers) = getEdhAttrWithMagic
            (AttrByName "@<-^")
            super
            key
            (getFromSupers restSupers)
            exit
      in  contEdhSTM
            $   readTVar (objSupers this)
            >>= runEdhProg pgs
            .   getFromSupers
    -- give super objects the magical power to intercept
    -- attribute access on descendant objects, via obj ref
    _ -> evalExpr fromExpr $ \(OriginalValue !fromVal _ _) -> case fromVal of
      (EdhObject !obj) -> do
        let noMagic :: EdhProg (STM ())
            noMagic = contEdhSTM $ resolveEdhObjAttr obj key >>= \case
              Nothing         -> runEdhProg pgs exitNoAttr
              Just !originVal -> exitEdhSTM' pgs exit originVal
        getEdhAttrWithMagic (AttrByName "@<-*") obj key noMagic exit
      _ ->
        throwEdh EvalError
          $  "Expecting an object but got a "
          <> T.pack (show $ edhTypeOf fromVal)
          <> ": "
          <> T.pack (show fromVal)


-- There're 2 tiers of magic happen during object attribute resolution in Edh.
--  *) a magical super controls its direct descendants in behaving as an object, by
--     intercepting the attr resolution
--  *) a metamagical super controls its direct descendants in behaving as a magical
--     super, by intercepting the magic method (as attr) resolution

getEdhAttrWithMagic
  :: AttrKey
  -> Object
  -> AttrKey
  -> EdhProg (STM ())
  -> EdhProcExit
  -> EdhProg (STM ())
getEdhAttrWithMagic !magicKey !obj !key !exitNoMagic !exit = do
  !pgs <- ask
  let
    getViaSupers :: [Object] -> EdhProg (STM ())
    getViaSupers [] = exitNoMagic
    getViaSupers (super : restSupers) =
      getEdhAttrWithMagic (AttrByName "!<-") super magicKey noMetamagic
        $ \(OriginalValue !magicMth _ _) ->
            contEdhSTM $ withMagicMethod magicMth
     where
      noMetamagic :: EdhProg (STM ())
      noMetamagic = contEdhSTM $ resolveEdhObjAttr super magicKey >>= \case
        Nothing -> runEdhProg pgs $ getViaSupers restSupers
        Just (OriginalValue !magicMth _ _) -> withMagicMethod magicMth
      withMagicMethod :: EdhValue -> STM ()
      withMagicMethod !magicMth =
        edhMakeCall pgs
                    magicMth
                    obj
                    [SendPosArg (GodSendExpr $ attrKeyValue key)]
          $ \mkCall ->
              runEdhProg pgs $ mkCall $ \(OriginalValue !magicRtn _ _) ->
                case magicRtn of
                  EdhContinue -> getViaSupers restSupers
                  _           -> exitEdhProc exit magicRtn
  contEdhSTM $ readTVar (objSupers obj) >>= runEdhProg pgs . getViaSupers

setEdhAttrWithMagic
  :: EdhProgState
  -> AttrKey
  -> Object
  -> AttrKey
  -> EdhValue
  -> EdhProg (STM ())
  -> EdhProcExit
  -> EdhProg (STM ())
setEdhAttrWithMagic !pgsAfter !magicKey !obj !key !val !exitNoMagic !exit = do
  !pgs <- ask
  contEdhSTM $ readTVar (objSupers obj) >>= runEdhProg pgs . setViaSupers
 where
  setViaSupers :: [Object] -> EdhProg (STM ())
  setViaSupers []                   = exitNoMagic
  setViaSupers (super : restSupers) = do
    !pgs <- ask
    getEdhAttrWithMagic (AttrByName "!<-")
                        super
                        magicKey
                        (setViaSupers restSupers)
      $ \(OriginalValue !magicMth _ _) ->
          contEdhSTM
            $ edhMakeCall
                pgs
                magicMth
                obj
                [ SendPosArg (GodSendExpr $ attrKeyValue key)
                , SendPosArg (GodSendExpr val)
                ]
            $ \mkCall ->
                runEdhProg pgs $ mkCall $ \(OriginalValue !magicRtn _ _) ->
                  case magicRtn of
                    EdhContinue -> setViaSupers restSupers
                    _ -> local (const pgsAfter) $ exitEdhProc exit magicRtn


setEdhAttr
  :: EdhProgState
  -> Expr
  -> AttrKey
  -> EdhValue
  -> EdhProcExit
  -> EdhProg (STM ())
setEdhAttr !pgsAfter !tgtExpr !key !val !exit = do
  !pgs <- ask
  let !(Scope _ !this !that _ _) = contextScope $ edh'context pgs
  case tgtExpr of
    -- give super objects the magical power to intercept
    -- attribute assignment to descendant objects, via `this` ref
    AttrExpr ThisRef ->
      let noMagic :: EdhProg (STM ())
          noMagic = contEdhSTM $ do
            modifyTVar' (objEntity this) $ setEntityAttr key val
            runEdhProg pgsAfter $ exitEdhProc exit val
      in  setEdhAttrWithMagic pgsAfter
                              (AttrByName "<-@")
                              this
                              key
                              val
                              noMagic
                              exit
    -- no magic layer laid over assignment via `that` ref
    AttrExpr ThatRef -> contEdhSTM $ do
      modifyTVar' (objEntity that) $ setEntityAttr key val
      runEdhProg pgsAfter $ exitEdhProc exit val
    -- not allowing assignment via super
    AttrExpr SuperRef -> throwEdh EvalError "Can not assign via super"
    -- give super objects the magical power to intercept
    -- attribute assignment to descendant objects, via obj ref
    _ -> evalExpr tgtExpr $ \(OriginalValue !tgtVal _ _) -> case tgtVal of
      EdhObject !tgtObj ->
        let noMagic :: EdhProg (STM ())
            noMagic = contEdhSTM $ do
              modifyTVar' (objEntity tgtObj) $ setEntityAttr key val
              runEdhProg pgsAfter $ exitEdhProc exit val
        in  setEdhAttrWithMagic pgsAfter
                                (AttrByName "*<-@")
                                tgtObj
                                key
                                val
                                noMagic
                                exit
      _ ->
        throwEdh EvalError
          $  "Invalid assignment target, it's a "
          <> T.pack (show $ edhTypeOf tgtVal)
          <> ": "
          <> T.pack (show tgtVal)


edhMakeCall
  :: EdhProgState
  -> EdhValue
  -> Object
  -> ArgsSender
  -> ((EdhProcExit -> EdhProg (STM ())) -> STM ())
  -> STM ()
edhMakeCall !pgsCaller !callee'val !callee'that !argsSndr !callMaker = do
  let !callerCtx   = edh'context pgsCaller
      !callerScope = contextScope callerCtx
  case callee'val of

    -- calling a host procedure
    (EdhHostProc (HostProcedure proc'name proc)) -> do
      procDecl <- hostProcDecl proc'name
      callMaker $ \exit -> do
      -- a host procedure runs against its caller's scope, with
      -- 'thatObject' changed to the resolution target object
        let !calleeScope =
              callerScope { thatObject = callee'that, scopeProc = procDecl }
            !calleeCtx = callerCtx
              { callStack       = calleeScope <| callStack callerCtx
              , generatorCaller = Nothing
              , contextMatch    = true
              , contextStmt     = voidStatement
              }
            !pgsCallee = pgsCaller { edh'context = calleeCtx }
        contEdhSTM
          -- insert a cycle tick here, so if no tx required for the call
          -- overall, the callee resolution tx stops here then the callee
          -- runs in next stm transaction
          $ flip (exitEdhSTM' pgsCallee) (wuji pgsCallee)
          $ \_ -> proc argsSndr $ \OriginalValue {..} ->
              -- return the result in CPS with caller pgs restored
              contEdhSTM $ exitEdhSTM pgsCaller exit valueFromOrigin

    -- calling a class (constructor) procedure
    (EdhClass cls) ->
      -- ensure atomicity of args sending
      runEdhProg pgsCaller { edh'in'tx = True }
        $ packEdhArgs pgsCaller argsSndr
        $ \apk -> contEdhSTM $ callMaker $ constructEdhObject apk cls

    -- calling a method procedure
    (EdhMethod (Method !mth'lexi'stack !mth'proc)) ->
      -- ensure atomicity of args sending
      runEdhProg pgsCaller { edh'in'tx = True }
        $ packEdhArgs pgsCaller argsSndr
        $ \apk -> contEdhSTM $ callMaker $ callEdhMethod apk
                                                         callee'that
                                                         mth'lexi'stack
                                                         mth'proc
                                                         Nothing

    -- calling an interpreter procedure
    (EdhInterpreter (Interpreter !mth'lexi'stack !mth'proc)) ->
      -- ensure atomicity of args sending
      runEdhProg pgsCaller { edh'in'tx = True }
        $ packEdhExprs argsSndr
        $ \(ArgsPack !args !kwargs) -> contEdhSTM $ do
            argCallerScope <- mkScopeWrapper (contextWorld callerCtx)
                                             (contextScope callerCtx)
            callMaker $ callEdhMethod
              (ArgsPack (EdhObject argCallerScope : args) kwargs)
              callee'that
              mth'lexi'stack
              mth'proc
              Nothing

    -- calling a host generator
    (EdhHostGenr _) -> throwEdhSTM
      pgsCaller
      EvalError
      "Can only call a host generator by for-from-do"

    -- calling a generator
    (EdhGenrDef _) -> throwEdhSTM
      pgsCaller
      EvalError
      "Can only call a generator method by for-from-do"

    _ ->
      throwEdhSTM pgsCaller EvalError
        $  "Can not call a "
        <> T.pack (show $ edhTypeOf callee'val)
        <> ": "
        <> T.pack (show callee'val)


constructEdhObject :: ArgsPack -> Class -> EdhProcExit -> EdhProg (STM ())
constructEdhObject !apk cls@(Class !cls'lexi'stack clsProc@(ProcDecl _ !ctor'args !ctor'body)) !exit
  = do
    pgs <- ask
    let !callerCtx   = edh'context pgs
        !calleeScope = NE.head cls'lexi'stack
        !recvCtx     = callerCtx { callStack       = cls'lexi'stack
                                 , generatorCaller = Nothing
                                 , contextMatch    = true
                                 , contextStmt     = voidStatement
                                 }
    recvEdhArgs recvCtx ctor'args apk $ \ent -> contEdhSTM $ do
      newThis <- viewAsEdhObject ent cls []
      let !ctorScope = calleeScope { scopeEntity = ent
                                   , thisObject  = newThis
                                   , thatObject  = newThis
                                   , lexiStack   = NE.toList cls'lexi'stack
                                   , scopeProc   = clsProc
                                   }
          !ctorCtx = callerCtx { callStack = ctorScope <| callStack callerCtx
                               , generatorCaller = Nothing
                               , contextMatch    = true
                               , contextStmt     = voidStatement
                               }
          !pgsCtor = pgs { edh'context = ctorCtx }
      runEdhProg pgsCtor
        $ evalStmt ctor'body
        $ \(OriginalValue !ctorRtn _ _) -> local (const pgs) $ case ctorRtn of
            -- allow a class procedure to explicitly return other
            -- value than newly constructed `this` object
            -- it can still `return this to early stop the ctor proc
            -- which is magically an advanced feature
            EdhReturn !rtnVal -> exitEdhProc exit rtnVal
            EdhContinue ->
              throwEdh EvalError "Unexpected continue from constructor"
            -- allow the use of `break` to early stop a constructor 
          -- allow the use of `break` to early stop a constructor 
            -- allow the use of `break` to early stop a constructor 
            -- procedure with nil result
            EdhBreak -> exitEdhProc exit nil
            -- no explicit return from class procedure, return the
            -- newly constructed this object, throw away the last
            -- value from the procedure execution
            _        -> exitEdhProc exit (EdhObject newThis)


callEdhMethod
  :: ArgsPack
  -> Object
  -> NonEmpty Scope
  -> ProcDecl
  -> Maybe EdhGenrCaller
  -> EdhProcExit
  -> EdhProg (STM ())
callEdhMethod !apk !callee'that !mth'lexi'stack mth'proc@(ProcDecl _ !mth'args !mth'body) !gnr'caller !exit
  = do
    !pgs <- ask
    let !callerCtx   = edh'context pgs
        !calleeScope = NE.head mth'lexi'stack
        !recvCtx     = callerCtx { callStack       = mth'lexi'stack
                                 , generatorCaller = Nothing
                                 , contextMatch    = true
                                 , contextStmt     = voidStatement
                                 }
    recvEdhArgs recvCtx mth'args apk $ \ent -> contEdhSTM $ do
      let !mthScope = calleeScope { scopeEntity = ent
                                  , thatObject  = callee'that
                                  , lexiStack   = NE.toList mth'lexi'stack
                                  , scopeProc   = mth'proc
                                  }
          !mthCtx = callerCtx { callStack = mthScope <| callStack callerCtx
                              , generatorCaller = gnr'caller
                              , contextMatch    = true
                              , contextStmt     = voidStatement
                              }
          !pgsMth = pgs { edh'context = mthCtx }
      runEdhProg pgsMth $ evalStmt mth'body $ \(OriginalValue !mthRtn _ _) ->
        local (const pgs) $ case mthRtn of
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


edhForLoop
  :: EdhProgState
  -> ArgsReceiver
  -> Expr
  -> Expr
  -> (EdhValue -> STM ())
  -> ((EdhProcExit -> EdhProg (STM ())) -> STM ())
  -> STM ()
edhForLoop !pgsLooper !argsRcvr !iterExpr !doExpr !iterCollector !forLooper =
  do
    let
      -- receive one yielded value from the generator, the 'genrCont' here is
      -- to continue the generator execution, result passed to the 'genrCont'
      -- here is the eval'ed value of the `yield` expression from the
      -- generator's perspective
      recvYield
        :: EdhProcExit -> EdhValue -> (EdhValue -> STM ()) -> EdhProg (STM ())
      recvYield !exit !yielded'val !genrCont = do
        pgs <- ask
        let !ctx   = edh'context pgs
            !scope = contextScope ctx
        case yielded'val of
          EdhContinue ->
            throwEdh EvalError "Unexpected continue from generator"
          EdhBreak -> throwEdh EvalError "Unexpected break from generator"
          _ ->
            recvEdhArgs
                ctx
                argsRcvr
                (case yielded'val of
                  EdhArgsPack apk -> apk
                  _               -> ArgsPack [yielded'val] Map.empty
                )
              $ \ent -> contEdhSTM $ do
                  em <- readTVar ent
                  modifyTVar' (scopeEntity scope) $ Map.union em
                  runEdhProg pgs
                    $ evalExpr doExpr
                    $ \(OriginalValue !doResult _ _) -> case doResult of
                        EdhContinue ->
                          -- propagate the continue to generator
                          contEdhSTM $ genrCont EdhContinue
                        EdhBreak ->
                          -- early stop the for-from-do with nil result
                          exitEdhProc exit nil
                        EdhReturn !rtnVal ->
                          -- early return from for-from-do
                          exitEdhProc exit (EdhReturn rtnVal)
                        _ -> contEdhSTM $ do
                          -- normal result from do, send to generator
                          iterCollector doResult
                          genrCont doResult

    runEdhProg pgsLooper $ case deParen iterExpr of
      CallExpr procExpr argsSndr -> -- loop over a generator
        evalExpr procExpr
          $ \(OriginalValue !callee'val !_callee'scope !callee'that) ->
              case callee'val of

                -- calling a host generator
                (EdhHostGenr (HostProcedure proc'name proc)) -> contEdhSTM $ do
                  procDecl <- hostProcDecl proc'name
                  forLooper $ \exit -> do
                    pgs <- ask
                    let !ctx   = edh'context pgs
                        !scope = contextScope ctx
                    -- a host procedure runs against its caller's scope, with
                    -- 'thatObject' changed to the resolution target object
                    let
                      !calleeScope =
                        scope { thatObject = callee'that, scopeProc = procDecl }
                      !calleeCtx = ctx
                        { callStack       = calleeScope <| callStack ctx
                        , generatorCaller = Just (pgs, recvYield exit)
                        , contextMatch    = true
                        , contextStmt     = voidStatement
                        }
                      !pgsCallee = pgs { edh'context = calleeCtx }
                    contEdhSTM
                      -- insert a cycle tick here, so if no tx required for the call
                      -- overall, the callee resolution tx stops here then the callee
                      -- runs in next stm transaction
                      $ flip (exitEdhSTM' pgsCallee) (wuji pgsCallee)
                      $ \_ -> proc argsSndr $ \OriginalValue {..} ->
                          contEdhSTM
                                -- return the result in CPS with caller pgs restored
                                     $ exitEdhSTM pgs exit valueFromOrigin

                -- calling a generator
                (EdhGenrDef (GenrDef !gnr'lexi'stack !gnr'proc)) ->
                  -- ensure atomicity of args sending
                  local (const pgsLooper { edh'in'tx = True })
                    $ packEdhArgs pgsLooper argsSndr
                    $ \apk -> contEdhSTM $ forLooper $ \exit -> do
                        pgs <- ask
                        callEdhMethod apk
                                      callee'that
                                      gnr'lexi'stack
                                      gnr'proc
                                      (Just (pgs, recvYield exit))
                          -- return the result in CPS with looper pgs restored
                          $ \OriginalValue {..} -> contEdhSTM $ exitEdhSTM
                              pgs
                              exit
                              valueFromOrigin

                _ ->
                  throwEdh EvalError
                    $ "Can only call a generator method from for-from-do, not a "
                    <> T.pack (show $ edhTypeOf callee'val)
                    <> ": "
                    <> T.pack (show callee'val)
      _ -> -- loop over an iterable value
           evalExpr iterExpr $ \(OriginalValue !iterVal _ _) ->
        contEdhSTM $ forLooper $ \exit -> do
          pgs <- ask
          let !ctx   = edh'context pgs
              !scope = contextScope ctx
          contEdhSTM $ do
            let -- do one iteration
              do1 :: ArgsPack -> STM () -> STM ()
              do1 !apk !next =
                runEdhProg pgs $ recvEdhArgs ctx argsRcvr apk $ \ent ->
                  contEdhSTM $ do
                    em <- readTVar ent
                    modifyTVar' (scopeEntity scope) $ Map.union em
                    runEdhProg pgs
                      $ evalExpr doExpr
                      $ \(OriginalValue !doResult _ _) -> case doResult of
                          EdhBreak ->
                            -- break for loop
                            exitEdhProc exit nil
                          EdhReturn rtnVal ->
                            -- early return during for loop
                            exitEdhProc exit rtnVal
                          _ -> contEdhSTM $ do
                            -- continue for loop
                            iterCollector doResult
                            next

              -- loop over a series of args packs
              iterThem :: [ArgsPack] -> STM ()
              iterThem []           = exitEdhSTM pgs exit nil
              iterThem (apk : apks) = do1 apk $ iterThem apks

              -- loop over a subscriber's channel of an event sink
              iterEvt :: TChan EdhValue -> STM ()
              iterEvt !subChan = waitEdhSTM pgs (readTChan subChan) $ \case
                EdhArgsPack apk -> do1 apk $ iterEvt subChan
                ev -> do1 (ArgsPack [ev] Map.empty) $ iterEvt subChan

            case iterVal of

              -- loop from an event sink
              (EdhSink sink) -> subscribeEvents sink >>= \(subChan, mrv) ->
                case mrv of
                  Nothing -> iterEvt subChan
                  Just ev ->
                    let apk = case ev of
                          EdhArgsPack apk_ -> apk_
                          _                -> ArgsPack [ev] Map.empty
                    in  do1 apk $ iterEvt subChan

              -- loop from a positonal-only args pack
              (EdhArgsPack (ArgsPack !args !kwargs)) | Map.null kwargs ->
                iterThem
                  [ case val of
                      EdhArgsPack apk' -> apk'
                      _                -> ArgsPack [val] Map.empty
                  | val <- args
                  ]

              -- loop from a keyword-only args pack
              (EdhArgsPack (ArgsPack !args !kwargs)) | null args ->
                iterThem
                  [ ArgsPack [EdhString k, v] $ Map.empty
                  | (k, v) <- Map.toList kwargs
                  ]

              -- loop from a tuple
              (EdhTuple vs) -> iterThem
                [ case val of
                    EdhArgsPack apk' -> apk'
                    _                -> ArgsPack [val] Map.empty
                | val <- vs
                ]

              -- loop from a list
              (EdhList (List l)) -> do
                ll <- readTVar l
                iterThem
                  [ case val of
                      EdhArgsPack apk' -> apk'
                      _                -> ArgsPack [val] Map.empty
                  | val <- ll
                  ]

              -- loop from a dict
              (EdhDict (Dict d)) -> do
                ds <- readTVar d
                iterThem -- don't be tempted to yield pairs from a dict here,
                    -- it'll be messy if some entry values are themselves pairs
                  [ ArgsPack [itemKeyValue k, v] Map.empty
                  | (k, v) <- Map.toList ds
                  ]

              _ ->
                throwEdhSTM pgsLooper EvalError
                  $  "Can not do a for loop from "
                  <> T.pack (show $ edhTypeOf iterVal)
                  <> ": "
                  <> T.pack (show iterVal)


-- | Make a reflective object wrapping the specified scope
--
-- todo currently only lexical context is recorded, the call frames may
--      be needed in the future
mkScopeWrapper :: EdhWorld -> Scope -> STM Object
mkScopeWrapper world scope = do
  -- use an object to wrap the scope entity
  entWrapper <- viewAsEdhObject (scopeEntity scope) wrapperClass []
  -- a scope wrapper object is itself a blank bucket, so the builtin scope
  -- manipulation methods are not shadowed by attributes in the scope. it
  -- can be used to store arbitrary attributes as a side effect
  wrapperEnt <- newTVar Map.empty
  viewAsEdhObject
    wrapperEnt
    wrapperClass
    [
  -- put the 'scopeSuper' object as the top super, from it the builtin
  -- scope manipulation methods are resolved
      scopeSuper world
  -- put the object wrapping the entity as the bottom super object, so attrs
  -- not shadowed by those manually assigned ones to 'wrapperEnt', or scope
  -- manipulation methods, can be read off directly from the wrapper object,
  -- caveat: you don't rely on this in writing attr reading Edh code, this
  -- is convenient for interactive human inspectors, but problematic for
  -- automatic code.
    , entWrapper
    ]
 where
  -- save the scope as top of 'classLexiStack' of the fake class for wrapper
  !wrapperClass =
    (objClass $ scopeSuper world) { classLexiStack = scope :| lexiStack scope }


-- | Assign an evaluated value to a target expression
--
-- Note the calling procedure should declare in-tx state in evaluating the
-- right-handle value as well as running this, so the evaluation of the
-- right-hand value as well as the writting to the target entity are done
-- within the same tx, thus for atomicity of the whole assignment.
assignEdhTarget
  :: EdhProgState -> Expr -> EdhProcExit -> EdhValue -> EdhProg (STM ())
assignEdhTarget !pgsAfter !lhExpr !exit !rhVal = do
  !pgs <- ask
  case lhExpr of
    AttrExpr !addr -> case addr of
      -- silently drop value assigned to single underscore
      DirectRef (NamedAttr "_") ->
        contEdhSTM $ runEdhProg pgsAfter $ exitEdhProc exit nil
      -- no magic imposed to direct assignment in a (possibly class) proc
      DirectRef !addr' -> contEdhSTM $ resolveAddr pgs addr' >>= \key -> do
        modifyTVar' (scopeEntity $ contextScope $ edh'context pgs)
          $ setEntityAttr key rhVal
        runEdhProg pgsAfter $ exitEdhProc exit rhVal
      -- assign to an addressed attribute
      IndirectRef !tgtExpr !addr' -> contEdhSTM $ do
        key <- resolveAddr pgs addr'
        runEdhProg pgs $ setEdhAttr pgsAfter tgtExpr key rhVal exit
      -- god forbidden things
      ThisRef  -> throwEdh EvalError "Can not assign to this"
      ThatRef  -> throwEdh EvalError "Can not assign to that"
      SuperRef -> throwEdh EvalError "Can not assign to super"
    -- dereferencing attribute assignment
    InfixExpr "$" !tgtExpr !addrRef ->
      evalExpr addrRef $ \(OriginalValue !addrVal _ _) -> case addrVal of
        EdhString !attrName ->
          setEdhAttr pgsAfter tgtExpr (AttrByName attrName) rhVal exit
        EdhSymbol !sym ->
          setEdhAttr pgsAfter tgtExpr (AttrBySym sym) rhVal exit
        _ ->
          throwEdh EvalError
            $  "Invalid attribute reference - "
            <> edhValueStr (edhTypeOf rhVal)
            <> ": "
            <> edhValueStr rhVal
    x ->
      throwEdh EvalError $ "Invalid left hand value for assignment: " <> T.pack
        (show x)


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
--     ***pkargs


recvEdhArgs
  :: Context
  -> ArgsReceiver
  -> ArgsPack
  -> (Entity -> EdhProg (STM ()))
  -> EdhProg (STM ())
recvEdhArgs !recvCtx !argsRcvr apk@(ArgsPack !posArgs !kwArgs) !exit = do
  !pgsCaller <- ask
  let -- args receive always done in callee's context with tx on
    !pgsRecv = pgsCaller { edh'in'tx = True, edh'context = recvCtx }
    recvFromPack
      :: (ArgsPack, EntityStore) -> ArgReceiver -> STM (ArgsPack, EntityStore)
    recvFromPack (pk@(ArgsPack posArgs' kwArgs'), em) argRcvr = case argRcvr of
      RecvRestPosArgs "_" ->
        -- silently drop the value to single underscore, while consume the args
        -- from incoming pack
        return (ArgsPack [] kwArgs', em)
      RecvRestPosArgs restPosArgAttr -> return
        ( ArgsPack [] kwArgs'
        , Map.insert (AttrByName restPosArgAttr)
                     (EdhArgsPack $ ArgsPack posArgs' Map.empty)
                     em
        )
      RecvRestKwArgs "_" ->
        -- silently drop the value to single underscore, while consume the args
        -- from incoming pack
        return (ArgsPack posArgs' Map.empty, em)
      RecvRestKwArgs restKwArgAttr -> return
        ( ArgsPack posArgs' Map.empty
        , Map.insert (AttrByName restKwArgAttr)
                     (EdhArgsPack $ ArgsPack [] kwArgs')
                     em
        )
      RecvRestPkArgs "_" ->
        -- silently drop the value to single underscore, while consume the args
        -- from incoming pack
        return (ArgsPack [] Map.empty, em)
      RecvRestPkArgs restPkArgAttr -> return
        ( ArgsPack [] Map.empty
        , Map.insert (AttrByName restPkArgAttr) (EdhArgsPack pk) em
        )
      RecvArg "_" _ _ -> do
        -- silently drop the value to single underscore, while consume the arg
        -- from incoming pack
        (_, posArgs'', kwArgs'') <- resolveArgValue "_" Nothing
        return (ArgsPack posArgs'' kwArgs'', em)
      RecvArg argName argTgtAddr argDefault -> do
        (argVal, posArgs'', kwArgs'') <- resolveArgValue argName argDefault
        case argTgtAddr of
          Nothing ->
            return
              ( ArgsPack posArgs'' kwArgs''
              , Map.insert (AttrByName argName) argVal em
              )
          Just (DirectRef addr) -> case addr of
            NamedAttr attrName -> -- simple rename
              return
                ( ArgsPack posArgs'' kwArgs''
                , Map.insert (AttrByName attrName) argVal em
                )
            SymbolicAttr symName -> -- todo support this ?
              throwEdhSTM pgsRecv EvalError
                $  "Do you mean `this.@"
                <> symName
                <> "` instead ?"
          Just addr@(IndirectRef _ _) -> do
            -- do assignment in callee's context, and return to caller's afterwards
            runEdhProg pgsRecv
              $ assignEdhTarget pgsCaller (AttrExpr addr) edhNop argVal
            return (ArgsPack posArgs'' kwArgs'', em)
          tgt ->
            throwEdhSTM pgsRecv EvalError
              $  "Invalid argument retarget: "
              <> T.pack (show tgt)
     where
      resolveArgValue
        :: AttrName
        -> Maybe Expr
        -> STM (EdhValue, [EdhValue], Map.Map AttrName EdhValue)
      resolveArgValue argName argDefault = do
        let (inKwArgs, kwArgs'') = takeOutFromMap argName kwArgs'
        case inKwArgs of
          Just argVal -> return (argVal, posArgs', kwArgs'')
          _           -> case posArgs' of
            (posArg : posArgs'') -> return (posArg, posArgs'', kwArgs'')
            []                   -> case argDefault of
              Just defaultExpr -> do
                defaultVar <- newEmptyTMVar
                -- always eval the default value atomically in callee's contex
                runEdhProg pgsRecv $ evalExpr
                  defaultExpr
                  (\OriginalValue {..} ->
                    contEdhSTM (putTMVar defaultVar valueFromOrigin)
                  )
                defaultVal <- readTMVar defaultVar
                return (defaultVal, posArgs', kwArgs'')
              _ ->
                throwEdhSTM pgsCaller EvalError
                  $  "Missing argument: "
                  <> argName
    woResidual :: ArgsPack -> EntityStore -> STM Entity
    woResidual (ArgsPack !posResidual !kwResidual) em
      | not (null posResidual)
      = throwEdhSTM pgsCaller EvalError
        $  "Extraneous "
        <> T.pack (show $ length posResidual)
        <> " positional argument(s)"
      | not (Map.null kwResidual)
      = throwEdhSTM pgsCaller EvalError
        $  "Extraneous keyword arguments: "
        <> T.unwords (Map.keys kwResidual)
      | otherwise
      = newTVar em
    doReturn :: Entity -> STM ()
    doReturn !ent =
      -- insert a cycle tick here, so if no tx required for the call
      -- overall, the args receiving tx stops here then the callee
      -- runs in next stm transaction
      exitEdhSTM' pgsCaller (\_ -> exit ent) (wuji pgsCaller)

  -- execution of the args receiving always in a tx for atomicity, and
  -- in the specified receiving (should be callee's outer) context
  local (const pgsRecv) $ case argsRcvr of
    PackReceiver argRcvrs -> contEdhSTM $ do
      (apk', em) <- foldM recvFromPack (apk, Map.empty) argRcvrs
      woResidual apk' em >>= doReturn
    SingleReceiver argRcvr -> contEdhSTM $ do
      (apk', em) <- recvFromPack (apk, Map.empty) argRcvr
      woResidual apk' em >>= doReturn
    WildReceiver -> contEdhSTM $ if null posArgs
      then newTVar (Map.mapKeys AttrByName kwArgs) >>= doReturn
      else
        throwEdhSTM pgsRecv EvalError
        $  "Unexpected "
        <> T.pack (show $ length posArgs)
        <> " positional argument(s) to wild receiver"


packHostProcArgs
  :: ArgsSender -> (ArgsPack -> EdhProg (STM ())) -> EdhProg (STM ())
packHostProcArgs !argsSender !exit = do
  !pgs <- ask
  -- a host procedure has its own call frame, underneath is the caller's stack
  let !pgsCaller = pgs { edh'context = callerCtx }
      !callerCtx = calleeCtx
        { callStack = case callerStack of
                        (top : rest) -> top :| rest
                        _ -> error "bug: host proc called from nowhere"
        }
      !callerStack = NE.tail $ callStack calleeCtx
      !calleeCtx   = edh'context pgs
  packEdhArgs pgsCaller argsSender exit


packEdhExprs
  :: [ArgSender] -> (ArgsPack -> EdhProg (STM ())) -> EdhProg (STM ())
packEdhExprs []       !exit = exit (ArgsPack [] Map.empty)
packEdhExprs (x : xs) !exit = case x of
  UnpackPosArgs _ -> throwEdh EvalError "unpack to expr not supported yet"
  UnpackKwArgs _ -> throwEdh EvalError "unpack to expr not supported yet"
  UnpackPkArgs _ -> throwEdh EvalError "unpack to expr not supported yet"
  SendPosArg !argExpr -> packEdhExprs xs $ \(ArgsPack !posArgs !kwArgs) ->
    exit (ArgsPack (EdhExpr argExpr : posArgs) kwArgs)
  SendKwArg !kw !argExpr -> packEdhExprs xs $ \(ArgsPack !posArgs !kwArgs) ->
    exit (ArgsPack posArgs $ Map.insert kw (EdhExpr argExpr) kwArgs)


packEdhArgs
  :: EdhProgState
  -> ArgsSender
  -> (ArgsPack -> EdhProg (STM ()))
  -> EdhProg (STM ())
packEdhArgs !pgsFrom !argsSender !exit = do
  !pgsAfter <- ask
  -- make sure values in a pack are evaluated in same tx
  local (const pgsFrom { edh'in'tx = True })
    $ packEdhArgs' argsSender
    $ \apk -> local (const pgsAfter) $ exit apk

packEdhArgs'
  :: [ArgSender] -> (ArgsPack -> EdhProg (STM ())) -> EdhProg (STM ())
packEdhArgs' []       !exit = exit (ArgsPack [] Map.empty)
packEdhArgs' (x : xs) !exit = do
  !pgs <- ask
  let edhVal2Kw :: EdhValue -> STM AttrName
      edhVal2Kw = \case
        EdhString s -> return s
        k ->
          throwEdhSTM pgs EvalError
            $  "Invalid argument keyword from value: "
            <> T.pack (show k)
      dictKey2Kw :: ItemKey -> STM AttrName
      dictKey2Kw = \case
        ItemByStr !name -> return name
        k ->
          throwEdhSTM pgs EvalError
            $  "Invalid argument keyword from dict key: "
            <> T.pack (show k)
  case x of
    UnpackPosArgs !posExpr -> evalExpr posExpr $ \OriginalValue {..} ->
      case valueFromOrigin of
        (EdhArgsPack (ArgsPack !posArgs' _kwArgs')) ->
          packEdhArgs' xs $ \(ArgsPack !posArgs !kwArgs) ->
            exit (ArgsPack (posArgs ++ posArgs') kwArgs)
        (EdhPair !k !v) -> packEdhArgs' xs $ \(ArgsPack !posArgs !kwArgs) ->
          exit (ArgsPack (posArgs ++ [k, v]) kwArgs)
        (EdhTuple !l) -> packEdhArgs' xs $ \(ArgsPack !posArgs !kwArgs) ->
          exit (ArgsPack (posArgs ++ l) kwArgs)
        (EdhList (List !l)) ->
          packEdhArgs' xs $ \(ArgsPack !posArgs !kwArgs) -> contEdhSTM $ do
            ll <- readTVar l
            runEdhProg pgs $ exit (ArgsPack (posArgs ++ ll) kwArgs)
        _ ->
          throwEdh EvalError
            $  "Can not unpack args from a "
            <> T.pack (show $ edhTypeOf valueFromOrigin)
            <> ": "
            <> T.pack (show valueFromOrigin)
    UnpackKwArgs !kwExpr -> evalExpr kwExpr $ \OriginalValue {..} ->
      case valueFromOrigin of
        EdhArgsPack (ArgsPack _posArgs' !kwArgs') ->
          packEdhArgs' xs $ \(ArgsPack !posArgs !kwArgs) ->
            exit (ArgsPack posArgs (Map.union kwArgs kwArgs'))
        (EdhPair !k !v) -> packEdhArgs' xs $ \case
          (ArgsPack !posArgs !kwArgs) -> contEdhSTM $ do
            kw <- edhVal2Kw k
            runEdhProg pgs $ exit (ArgsPack posArgs $ Map.insert kw v kwArgs)
        (EdhDict (Dict !ds)) -> packEdhArgs' xs $ \case
          (ArgsPack !posArgs !kwArgs) -> contEdhSTM $ do
            dm  <- readTVar ds
            kvl <- forM (Map.toAscList dm) $ \(k, v) -> (, v) <$> dictKey2Kw k
            runEdhProg pgs $ exit
              (ArgsPack posArgs $ Map.union kwArgs $ Map.fromAscList kvl)
        _ ->
          throwEdh EvalError
            $  "Can not unpack kwargs from a "
            <> T.pack (show $ edhTypeOf valueFromOrigin)
            <> ": "
            <> T.pack (show valueFromOrigin)
    UnpackPkArgs !pkExpr -> evalExpr pkExpr $ \OriginalValue {..} ->
      case valueFromOrigin of
        (EdhArgsPack (ArgsPack !posArgs' !kwArgs')) -> packEdhArgs' xs $ \case
          (ArgsPack !posArgs !kwArgs) ->
            exit (ArgsPack (posArgs ++ posArgs') (Map.union kwArgs kwArgs'))
        _ ->
          throwEdh EvalError
            $  "Can not unpack pkargs from a "
            <> T.pack (show $ edhTypeOf valueFromOrigin)
            <> ": "
            <> T.pack (show valueFromOrigin)
    SendPosArg !argExpr ->
      evalExpr argExpr
        $ \OriginalValue {..} ->
            packEdhArgs' xs $ \(ArgsPack !posArgs !kwArgs) ->
              exit (ArgsPack (valueFromOrigin : posArgs) kwArgs)
    SendKwArg !kw !argExpr -> evalExpr argExpr $ \OriginalValue {..} ->
      packEdhArgs' xs $ \pk@(ArgsPack !posArgs !kwArgs) -> case kw of
        "_" ->
          -- silently drop the value to keyword of single underscore
          exit pk
        _ -> exit
          (ArgsPack posArgs $ Map.alter
            (\case -- make sure latest value with same kw take effect
              Nothing        -> Just valueFromOrigin
              Just !laterVal -> Just laterVal
            )
            kw
            kwArgs
          )

