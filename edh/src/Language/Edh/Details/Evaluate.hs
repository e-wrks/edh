
module Language.Edh.Details.Evaluate where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Control.Concurrent.STM

import           Data.Unique
import           Data.Maybe
import qualified Data.ByteString               as B
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Text.Encoding
import           Data.Text.Encoding.Error
import qualified Data.HashMap.Strict           as Map
import           Data.List.NonEmpty             ( NonEmpty(..)
                                                , (<|)
                                                )

import           Text.Megaparsec

import           Language.Edh.Control
import           Language.Edh.Parser
import           Language.Edh.Event
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.PkgMan
import           Language.Edh.Details.Utils


parseEdh :: EdhWorld -> String -> Text -> STM (Either ParserError [StmtSrc])
parseEdh !world !srcName !srcCode = do
  pd <- takeTMVar wops -- update 'worldOperators' atomically wrt parsing
  let (pr, pd') = runState (runParserT parseProgram srcName srcCode) pd
  case pr of
    -- update operator precedence dict on success of parsing
    Right _ -> putTMVar wops pd'
    _       -> pure ()
  return pr
  where !wops = worldOperators world


evalEdh :: String -> Text -> EdhProcExit -> EdhProg (STM ())
evalEdh !srcName !srcCode !exit = do
  pgs <- ask
  let ctx   = edh'context pgs
      world = contextWorld ctx
  contEdhSTM $ parseEdh world srcName srcCode >>= \case
    Left  !err   -> throwSTM $ ParseError err $ getEdhCallContext pgs
    Right !stmts -> runEdhProg pgs $ evalBlock stmts exit


deParen :: Expr -> Expr
deParen x = case x of
  ParenExpr x' -> deParen x'
  _            -> x

evalStmt :: StmtSrc -> EdhProcExit -> EdhProg (STM ())
evalStmt ss@(StmtSrc (_sp, !stmt)) !exit = ask >>= \pgs ->
  local (const pgs { edh'context = (edh'context pgs) { contextStmt = ss } })
    $ evalStmt' stmt
    $ \rtn -> local (const pgs) $ exitEdhProc' exit rtn


evalCaseBlock :: Expr -> EdhProcExit -> EdhProg (STM ())
evalCaseBlock !expr !exit = case expr of
  -- case-of with a block is normal
  BlockExpr stmts' -> evalBlock stmts' exit
  -- single branch case is some special
  _                -> evalExpr expr $ \(OriginalValue !val _ _) -> case val of
    -- the only branch does match
    (EdhCaseClose !v) -> exitEdhProc exit v
    -- the only branch does not match
    EdhFallthrough    -> exitEdhProc exit nil
    -- ctrl to be propagated outwards
    EdhBreak          -> exitEdhProc exit EdhBreak
    EdhContinue       -> exitEdhProc exit EdhContinue
    (EdhReturn !v)    -> exitEdhProc exit (EdhReturn v)
    -- yield should have been handled by 'evalExpr'
    (EdhYield  _ )    -> throwEdh EvalError "bug yield reached block"
    -- the only expr has no special branching result, propagate as is
    _                 -> exitEdhProc exit val

evalBlock :: [StmtSrc] -> EdhProcExit -> EdhProg (STM ())
evalBlock []    !exit = exitEdhProc exit nil
evalBlock [!ss] !exit = evalStmt ss $ \(OriginalValue !val _ _) -> case val of
  -- last branch does match
  (EdhCaseClose !v) -> exitEdhProc exit v
  -- explicit `fallthrough` at end of this block, cascade to outer block
  EdhFallthrough    -> exitEdhProc exit EdhFallthrough
  -- ctrl to be propagated outwards
  EdhBreak          -> exitEdhProc exit EdhBreak
  EdhContinue       -> exitEdhProc exit EdhContinue
  (EdhReturn !v)    -> exitEdhProc exit (EdhReturn v)
  -- yield should have been handled by 'evalExpr'
  (EdhYield  _ )    -> throwEdh EvalError "bug yield reached block"
  -- last stmt has no special branching result, propagate as is
  _                 -> exitEdhProc exit val
evalBlock (ss : rest) !exit = evalStmt ss $ \(OriginalValue !val _ _) ->
  case val of
    -- this branch matches without fallthrough, done this block
    (EdhCaseClose !v) -> exitEdhProc exit v
    -- should fallthrough to next branch (or stmt)
    EdhFallthrough    -> evalBlock rest exit
    -- ctrl to be propagated outwards
    EdhBreak          -> exitEdhProc exit EdhBreak
    EdhContinue       -> exitEdhProc exit EdhContinue
    (EdhReturn !v)    -> exitEdhProc exit (EdhReturn v)
    -- yield should have been handled by 'evalExpr'
    (EdhYield  _ )    -> throwEdh EvalError "bug yield reached block"
    -- no special branching result, continue this block
    _                 -> evalBlock rest exit


-- | a left-to-right expr list eval'er, returning a tuple
evalExprs :: [Expr] -> EdhProcExit -> EdhProg (STM ())
-- here 'EdhTuple' is used for intermediate tag,
-- not returning actual tuple values as in Edh.
evalExprs []       !exit = exitEdhProc exit (EdhTuple [])
evalExprs (x : xs) !exit = evalExpr x $ \(OriginalValue !val _ _) ->
  evalExprs xs $ \(OriginalValue !tv _ _) -> case tv of
    EdhTuple l -> exitEdhProc exit (EdhTuple (val : l))
    _          -> error "bug"


evalStmt' :: Stmt -> EdhProcExit -> EdhProg (STM ())
evalStmt' !stmt !exit = do
  !pgs <- ask
  let !ctx                   = edh'context pgs
      !world                 = contextWorld ctx
      (StmtSrc (!srcPos, _)) = contextStmt ctx
      !scope                 = contextScope ctx
  case stmt of

    ExprStmt expr -> evalExpr expr exit

    LetStmt argsRcvr argsSndr ->
      -- ensure args sending and receiving happens within a same tx
      -- for atomicity of the let statement
      local (const pgs { edh'in'tx = True }) $ packEdhArgs argsSndr $ \pk ->
        recvEdhArgs ctx argsRcvr pk $ \um -> contEdhSTM $ do
          -- overwrite current scope entity with attributes from the
          -- received entity
          updateEntityAttrs pgs (scopeEntity scope) $ Map.toList um
          -- let statement evaluates to nil always, with previous tx
          -- state restored
          exitEdhSTM pgs exit nil

    BreakStmt       -> exitEdhProc exit EdhBreak
    ContinueStmt    -> exitEdhProc exit EdhContinue
    FallthroughStmt -> exitEdhProc exit EdhFallthrough

    ReturnStmt expr -> evalExpr expr
      $ \(OriginalValue !val _ _) -> exitEdhProc exit (EdhReturn val)


    AtoIsoStmt expr ->
      contEdhSTM
        $ runEdhProg pgs { edh'in'tx = True } -- ensure in'tx state
        $ evalExpr expr
        $ \(OriginalValue !val _ _) -> -- restore original tx state
                                       contEdhSTM $ exitEdhSTM pgs exit val


    GoStmt expr -> case expr of

      CaseExpr tgtExpr branchesExpr ->
        evalExpr tgtExpr $ \(OriginalValue !val _ _) ->
          forkEdh exit
            $ contEdhSTM
            $ runEdhProg pgs { edh'context = ctx { contextMatch = val } }
             -- eval the branch(es) expr with the case target being the 'contextMatch'
            $ evalCaseBlock branchesExpr edhEndOfProc

      (CallExpr procExpr argsSndr) ->
        evalExpr procExpr $ \(OriginalValue !callee'val _ !callee'that) ->
          contEdhSTM
            $ edhMakeCall pgs callee'val callee'that argsSndr
            $ \mkCall -> runEdhProg pgs $ forkEdh exit (mkCall edhEndOfProc)

      (ForExpr argsRcvr iterExpr doExpr) ->
        contEdhSTM
          $ edhForLoop pgs argsRcvr iterExpr doExpr (const $ return ())
          $ \runLoop -> runEdhProg pgs $ forkEdh exit (runLoop edhEndOfProc)

      _ -> forkEdh exit $ evalExpr expr edhEndOfProc

    DeferStmt expr -> do
      let schedDefered :: EdhProgState -> EdhProg (STM ()) -> STM ()
          schedDefered pgs' prog = do
            modifyTVar' (edh'defers pgs) ((pgs', prog) :)
            exitEdhSTM pgs exit nil
      case expr of

        CaseExpr tgtExpr branchesExpr ->
          evalExpr tgtExpr $ \(OriginalValue !val _ _) ->
            contEdhSTM
              $ schedDefered pgs { edh'context = ctx { contextMatch = val } }
              -- eval the branch(es) expr with the case target being the 'contextMatch'
              $ evalCaseBlock branchesExpr edhEndOfProc

        (CallExpr procExpr argsSndr) ->
          evalExpr procExpr $ \(OriginalValue callee'val _ callee'that) ->
            contEdhSTM
              $ edhMakeCall pgs callee'val callee'that argsSndr
              $ \mkCall -> schedDefered pgs (mkCall edhEndOfProc)

        (ForExpr argsRcvr iterExpr doExpr) ->
          contEdhSTM
            $ edhForLoop pgs argsRcvr iterExpr doExpr (const $ return ())
            $ \runLoop -> schedDefered pgs (runLoop edhEndOfProc)

        _ -> contEdhSTM $ schedDefered pgs $ evalExpr expr edhEndOfProc


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
            <> T.pack (edhTypeNameOf val)
            <> ": "
            <> T.pack (show val)


    -- TODO impl. this
    -- TryStmt trunkStmt catchesList finallyStmt -> undefined
    -- ThrowStmt excExpr                         -> undefined


    WhileStmt cndExpr bodyExpr -> do
      let doWhile :: EdhProg (STM ())
          doWhile = evalExpr cndExpr $ \(OriginalValue !cndVal _ _) ->
            case cndVal of
              (EdhBool True) ->
                evalExpr bodyExpr $ \(OriginalValue !blkVal _ _) ->
                  case blkVal of
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
                  <> T.pack (edhTypeNameOf cndVal)
                  <> ": "
                  <> T.pack (show cndVal)
      doWhile

    ExtendsStmt superExpr ->
      evalExpr superExpr $ \(OriginalValue !superVal _ _) -> case superVal of
        (EdhObject !superObj) -> contEdhSTM $ do
          let
            !this       = thisObject scope
            !magicSpell = AttrByName "<-^"
            noMagic :: EdhProg (STM ())
            noMagic =
              contEdhSTM $ lookupEdhObjAttr pgs superObj magicSpell >>= \case
                EdhNil    -> exitEdhSTM pgs exit nil
                !magicMth -> withMagicMethod magicMth
            withMagicMethod :: EdhValue -> STM ()
            withMagicMethod magicMth = case magicMth of
              EdhNil              -> exitEdhSTM pgs exit nil
              EdhMethod !mth'proc -> do
                scopeObj <- mkScopeWrapper ctx $ objectScope ctx this
                runEdhProg pgs
                  $ callEdhMethod this
                                  mth'proc
                                  (ArgsPack [EdhObject scopeObj] Map.empty)
                  $ \_ -> contEdhSTM $ exitEdhSTM pgs exit nil
              _ ->
                throwEdhSTM pgs EvalError
                  $  "Invalid magic (<-^) method type: "
                  <> T.pack (edhTypeNameOf magicMth)
          modifyTVar' (objSupers this) (superObj :)
          runEdhProg pgs
            $ getEdhAttrWithMagic edhMetaMagicSpell superObj magicSpell noMagic
            $ \(OriginalValue !magicMth _ _) ->
                contEdhSTM $ withMagicMethod magicMth
        _ ->
          throwEdh EvalError
            $  "Can only extends an object, not "
            <> T.pack (edhTypeNameOf superVal)
            <> ": "
            <> T.pack (show superVal)

    ClassStmt pd@(ProcDecl name _ _) -> contEdhSTM $ do
      u <- unsafeIOToSTM newUnique
      let !cls = EdhClass ProcDefi { procedure'uniq = u
                                   , procedure'lexi = Just scope
                                   , procedure'decl = pd
                                   }
      when (name /= "_")
        $ changeEntityAttr pgs (scopeEntity scope) (AttrByName name) cls
      exitEdhSTM pgs exit cls

    MethodStmt pd@(ProcDecl name _ _) -> contEdhSTM $ do
      u <- unsafeIOToSTM newUnique
      let mth = EdhMethod ProcDefi { procedure'uniq = u
                                   , procedure'lexi = Just scope
                                   , procedure'decl = pd
                                   }
      when (name /= "_")
        $ changeEntityAttr pgs (scopeEntity scope) (AttrByName name) mth
      exitEdhSTM pgs exit mth

    GeneratorStmt pd@(ProcDecl name _ _) -> contEdhSTM $ do
      u <- unsafeIOToSTM newUnique
      let gdf = EdhGnrtor ProcDefi { procedure'uniq = u
                                   , procedure'lexi = Just scope
                                   , procedure'decl = pd
                                   }
      when (name /= "_")
        $ changeEntityAttr pgs (scopeEntity scope) (AttrByName name) gdf
      exitEdhSTM pgs exit gdf

    InterpreterStmt pd@(ProcDecl name _ _) -> contEdhSTM $ do
      u <- unsafeIOToSTM newUnique
      let mth = EdhIntrpr ProcDefi { procedure'uniq = u
                                   , procedure'lexi = Just scope
                                   , procedure'decl = pd
                                   }
      when (name /= "_")
        $ changeEntityAttr pgs (scopeEntity scope) (AttrByName name) mth
      exitEdhSTM pgs exit mth

    ProducerStmt pd@(ProcDecl name args _) -> contEdhSTM $ do
      u <- unsafeIOToSTM newUnique
      let mth = EdhPrducr ProcDefi { procedure'uniq = u
                                   , procedure'lexi = Just scope
                                   , procedure'decl = pd
                                   }
      unless (receivesNamedArg "outlet" args) $ throwEdhSTM
        pgs
        EvalError
        "a producer procedure should receive a `outlet` keyword argument"
      when (name /= "_")
        $ changeEntityAttr pgs (scopeEntity scope) (AttrByName name) mth
      exitEdhSTM pgs exit mth

    OpDeclStmt opSym opPrec opProc@(ProcDecl _ _ !pb) -> case pb of
      -- support re-declaring an existing operator to another name,
      -- with possibly a different precedence
      Left (StmtSrc (_, ExprStmt (AttrExpr (DirectRef (NamedAttr !origOpSym)))))
        -> contEdhSTM $ do
          origOp <- lookupEdhCtxAttr pgs scope (AttrByName origOpSym) >>= \case
            EdhNil ->
              throwEdhSTM pgs EvalError
                $  "Original operator ("
                <> origOpSym
                <> ") not in scope"
            op@EdhOprtor{} -> return op
            val ->
              throwEdhSTM pgs EvalError
                $  "Can not re-declare a "
                <> T.pack (edhTypeNameOf val)
                <> ": "
                <> T.pack (show val)
                <> " as an operator"
          changeEntityAttr pgs (scopeEntity scope) (AttrByName opSym) origOp
          exitEdhSTM pgs exit origOp
      _ -> contEdhSTM $ do
        validateOperDecl pgs opProc
        u <- unsafeIOToSTM newUnique
        let op = EdhOprtor
              opPrec
              Nothing
              ProcDefi { procedure'uniq = u
                       , procedure'lexi = Just scope
                       , procedure'decl = opProc
                       }
        changeEntityAttr pgs (scopeEntity scope) (AttrByName opSym) op
        exitEdhSTM pgs exit op

    OpOvrdStmt opSym opProc opPrec -> contEdhSTM $ do
      validateOperDecl pgs opProc
      let
        findPredecessor :: STM (Maybe EdhValue)
        findPredecessor =
          lookupEdhCtxAttr pgs scope (AttrByName opSym) >>= \case
            EdhNil -> -- do
              -- (EdhRuntime logger _) <- readTMVar $ worldRuntime world
              -- logger 30 (Just $ sourcePosPretty srcPos)
              --   $ ArgsPack
              --       [EdhString "overriding an unavailable operator"]
              --       Map.empty
              return Nothing
            op@EdhOprtor{} -> return $ Just op
            opVal          -> do
              (runtimeLogger $ worldRuntime world)
                  30
                  (Just $ sourcePosPretty srcPos)
                $ ArgsPack
                    [ EdhString
                      $  "overriding an invalid operator "
                      <> T.pack (edhTypeNameOf opVal)
                      <> ": "
                      <> T.pack (show opVal)
                    ]
                    Map.empty
              return Nothing
      predecessor <- findPredecessor
      u           <- unsafeIOToSTM newUnique
      let op = EdhOprtor
            opPrec
            predecessor
            ProcDefi { procedure'uniq = u
                     , procedure'lexi = Just scope
                     , procedure'decl = opProc
                     }
      changeEntityAttr pgs (scopeEntity scope) (AttrByName opSym) op
      exitEdhSTM pgs exit op

    ImportStmt argsRcvr srcExpr -> case srcExpr of
      LitExpr (StringLiteral importSpec) ->
        -- import from specified path
        importEdhModule' argsRcvr importSpec exit
      _ -> evalExpr srcExpr $ \(OriginalValue !srcVal _ _) -> case srcVal of
        EdhObject fromObj ->
          -- import from an object
          importFromObject argsRcvr fromObj exit
        _ ->
          -- todo support more sources of import ?
          throwEdh EvalError
            $  "Don't know how to import from a "
            <> T.pack (edhTypeNameOf srcVal)
            <> ": "
            <> T.pack (show srcVal)

    VoidStmt -> exitEdhProc exit nil

    _ -> throwEdh EvalError $ "Eval not yet impl for: " <> T.pack (show stmt)


importFromObject :: ArgsReceiver -> Object -> EdhProcExit -> EdhProg (STM ())
importFromObject !argsRcvr !fromObj !exit = do
  pgs <- ask
  let !ctx  = edh'context pgs
      !this = thisObject $ contextScope ctx
  contEdhSTM $ do
    ps <- allEntityAttrs pgs $ objEntity fromObj
    let !artsPk = ArgsPack [] $ Map.fromList $ catMaybes
          [ case k of
-- only attributes with a name not started with `_` are importable,
-- and all symbol values are not importable however named
              AttrByName attrName | not (T.isPrefixOf "_" attrName) -> case v of
                EdhSymbol _ -> Nothing
                _           -> Just (attrName, v)
-- symbolic attributes are effective stripped off, this is desirable so that
-- symbolic attributes are not importable, thus private to a module/object
              _ -> Nothing
          | (k, v) <- ps
          ]
    runEdhProg pgs $ recvEdhArgs ctx argsRcvr artsPk $ \em -> contEdhSTM $ do
      updateEntityAttrs pgs (objEntity this) $ Map.toList em
      exitEdhSTM pgs exit (EdhObject fromObj)

importEdhModule' :: ArgsReceiver -> Text -> EdhProcExit -> EdhProg (STM ())
importEdhModule' !argsRcvr !importSpec !exit =
  importEdhModule importSpec $ \(OriginalValue !moduVal _ _) -> case moduVal of
    EdhObject !modu -> importFromObject argsRcvr modu exit
    _               -> error "bug"

importEdhModule :: Text -> EdhProcExit -> EdhProg (STM ())
importEdhModule !impSpec !exit = do
  pgs <- ask
  let
    !ctx   = edh'context pgs
    !world = contextWorld ctx
    !scope = contextScope ctx
    importFromFS :: STM ()
    importFromFS = lookupEdhCtxAttr pgs scope (AttrByName "__file__") >>= \case
      EdhString !fromModuPath -> do
        (nomPath, moduFile) <-
          unsafeIOToSTM $ withEdhErrContext pgs $ locateEdhModule
            (edhPkgPathFrom $ T.unpack fromModuPath)
            (T.unpack impSpec)
        let !moduId = T.pack nomPath
        moduMap' <- takeTMVar (worldModules world)
        case Map.lookup moduId moduMap' of
          Just !moduSlot -> do
            -- put back immediately
            putTMVar (worldModules world) moduMap'
            -- blocking wait the target module loaded
            waitEdhSTM pgs (readTMVar moduSlot) $ \case
              -- TODO GHC should be able to detect cyclic imports as 
              --      deadlock, find ways to report that more friendly
              modu@EdhObject{} -> exitEdhSTM pgs exit modu
              importError -> -- the first importer failed loading it,
                -- replicate the error in this thread
                throwEdhSTM pgs EvalError $ T.pack $ show importError
          Nothing -> do -- we are the first importer
            -- allocate an empty slot
            moduSlot <- newEmptyTMVar
            -- put it for global visibility
            putTMVar (worldModules world) $ Map.insert moduId moduSlot moduMap'
            catchSTM -- TODO impl. Edh error handling
                ( loadModule pgs moduSlot moduId moduFile
                $ \(OriginalValue !result _ _) -> case result of
                    -- successfully loaded
                    modu@EdhObject{} -> exitEdhProc exit modu
                    _                -> error "bug"
                )
            -- TODO catchSTM does NOT work across Edh transactions,
            --      need to impl. a catchEdh or sth. to be used here.
              $ \(e :: SomeException) -> do
                  -- cleanup on loading error
                  let errStr = T.pack $ show e
                  void $ tryPutTMVar moduSlot $ EdhString errStr
                  moduMap'' <- takeTMVar (worldModules world)
                  case Map.lookup moduId moduMap'' of
                    Nothing        -> putTMVar (worldModules world) moduMap''
                    Just moduSlot' -> if moduSlot' == moduSlot
                      then putTMVar (worldModules world)
                        $ Map.delete moduId moduMap''
                      else putTMVar (worldModules world) moduMap''
                  throwSTM e
      _ -> error "bug: no valid `__file__` in context"
  if edh'in'tx pgs
    then throwEdh EvalError "You don't import from within a transaction"
    else contEdhSTM $ do
      moduMap <- readTMVar (worldModules world)
      case Map.lookup impSpec moduMap of
        -- attempt the import specification as direct module id first
        Just !moduSlot -> readTMVar moduSlot >>= \case
          modu@EdhObject{} -> exitEdhSTM pgs exit modu
          importError -> throwEdhSTM pgs EvalError $ T.pack $ show importError
        -- resolving to `.edh` source files from local filesystem
        Nothing -> importFromFS

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
  else do
    fileContent <-
      unsafeIOToSTM $ streamDecodeUtf8With lenientDecode <$> B.readFile moduFile
    case fileContent of
      Some !moduSource _ _ -> do
        modu <- createEdhModule' world moduId moduFile
        runEdhProg pgs { edh'context = moduleContext world modu }
          $ evalEdh moduFile moduSource
          $ \_ -> contEdhSTM $ do
              -- arm the successfully loaded module
              putTMVar moduSlot $ EdhObject modu
              -- switch back to module importer's scope and continue
              exitEdhSTM pgs exit (EdhObject modu)
 where
  ctx   = edh'context pgs
  world = contextWorld ctx

createEdhModule' :: EdhWorld -> ModuleId -> String -> STM Object
createEdhModule' !world !moduId !srcName = do
  -- prepare the module meta data
  !moduEntity <- createHashEntity $ Map.fromList
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
                    , procedure'lexi = Just $ worldScope world
                    , procedure'decl = ProcDecl
                      { procedure'name = "module:" <> moduId
                      , procedure'args = PackReceiver []
                      , procedure'body = Left $ StmtSrc
                                           ( SourcePos { sourceName   = srcName
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
  { callStack = objectScope worldCtx modu <| callStack worldCtx
  }
  where !worldCtx = worldContext world


evalExpr :: Expr -> EdhProcExit -> EdhProg (STM ())
evalExpr expr exit = do
  !pgs <- ask
  let !ctx                   = edh'context pgs
      !world                 = contextWorld ctx
      !genr'caller           = generatorCaller ctx
      (StmtSrc (!srcPos, _)) = contextStmt ctx
      !scope                 = contextScope ctx
  case expr of

    GodSendExpr !val    -> exitEdhProc exit val
    ExprWithSrc !x !src -> contEdhSTM $ do
      u <- unsafeIOToSTM newUnique
      exitEdhSTM pgs exit $ EdhExpr u x src

    LitExpr lit -> case lit of
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
            <> T.pack (edhTypeNameOf val)
            <> ": "
            <> T.pack (show val)
            <> " ❌"
      Not -> evalExpr expr' $ \(OriginalValue !val _ _) -> case val of
        (EdhBool v) -> exitEdhProc exit (EdhBool $ not v)
        _ ->
          throwEdh EvalError
            $  "Expect bool but got a "
            <> T.pack (edhTypeNameOf val)
            <> ": "
            <> T.pack (show val)
            <> " ❌"
      Guard -> contEdhSTM $ do
        (runtimeLogger $ worldRuntime world)
          30
          (Just $ sourcePosPretty srcPos)
          (ArgsPack [EdhString "Standalone guard treated as plain value."]
                    Map.empty
          )
        runEdhProg pgs $ evalExpr expr' exit

    IfExpr cond cseq alt -> evalExpr cond $ \(OriginalValue !val _ _) ->
      case val of
        (EdhBool True ) -> evalExpr cseq exit
        (EdhBool False) -> case alt of
          Just elseClause -> evalExpr elseClause exit
          _               -> exitEdhProc exit nil
        _ ->
          -- we are so strongly typed
          throwEdh EvalError
            $  "Expecting a boolean value but got a "
            <> T.pack (edhTypeNameOf val)
            <> ": "
            <> T.pack (show val)
            <> " ❌"

    DictExpr xs -> -- make sure dict k:v pairs are evaluated in same tx
      local (\s -> s { edh'in'tx = True })
        $ evalExprs xs
        $ \(OriginalValue !tv _ _) -> case tv of
            EdhTuple l -> contEdhSTM $ do
              dpl <- forM l $ \case
                EdhPair kVal vVal -> return (kVal, vVal)
                pv ->
                  throwEdhSTM pgs EvalError
                    $  "Invalid dict entry "
                    <> T.pack (edhTypeNameOf pv)
                    <> ": "
                    <> T.pack (show pv)
                    <> " ❌"
              ds <- newTVar $ Map.fromList dpl
              u  <- unsafeIOToSTM newUnique
              exitEdhSTM pgs exit (EdhDict (Dict u ds))
            _ -> error "bug"

    ListExpr xs -> -- make sure list values are evaluated in same tx
      local (\s -> s { edh'in'tx = True })
        $ evalExprs xs
        $ \(OriginalValue !tv _ _) -> case tv of
            EdhTuple l -> contEdhSTM $ do
              ll <- newTVar l
              u  <- unsafeIOToSTM newUnique
              exitEdhSTM pgs exit (EdhList $ List u ll)
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

    CaseExpr tgtExpr branchesExpr ->
      evalExpr tgtExpr $ \(OriginalValue !tgtVal _ _) ->
        -- eval the branch(es) expr with the case target being the 'contextMatch'
        local (const pgs { edh'context = ctx { contextMatch = tgtVal } })
          $ evalCaseBlock branchesExpr
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
        !key <- resolveEdhAttrAddr pgs addr'
        lookupEdhCtxAttr pgs scope key >>= \case
          EdhNil ->
            throwEdhSTM pgs EvalError $ "Not in scope: " <> T.pack (show addr')
          !val -> exitEdhSTM pgs exit val
      IndirectRef !tgtExpr !addr' -> contEdhSTM $ do
        key <- resolveEdhAttrAddr pgs addr'
        runEdhProg pgs $ getEdhAttr
          tgtExpr
          key
          (\tgtVal ->
            throwEdh EvalError
              $  "No such attribute "
              <> T.pack (show key)
              <> " from "
              <> T.pack (show tgtVal)
          )
          exit


    IndexExpr ixExpr tgtExpr ->
      evalExpr ixExpr $ \(OriginalValue !ixVal _ _) ->
        evalExpr tgtExpr $ \(OriginalValue !tgtVal _ _) -> case tgtVal of

        -- indexing a dict
          (EdhDict (Dict _ !d)) -> contEdhSTM $ do
            ds <- readTVar d
            case Map.lookup ixVal ds of
              Nothing  -> exitEdhSTM pgs exit nil
              Just val -> exitEdhSTM pgs exit val

          -- indexing an object, by calling its ([]) method with ixVal as the single arg
          (EdhObject obj) ->
            contEdhSTM $ lookupEdhObjAttr pgs obj (AttrByName "[]") >>= \case

              EdhNil ->
                throwEdhSTM pgs EvalError $ "No ([]) method from: " <> T.pack
                  (show obj)

              EdhMethod !mth'proc -> runEdhProg pgs
                $ callEdhMethod obj mth'proc (ArgsPack [ixVal] Map.empty) exit

              !badIndexer ->
                throwEdhSTM pgs EvalError
                  $  "Malformed index method ([]) on "
                  <> T.pack (show obj)
                  <> " - "
                  <> T.pack (edhTypeNameOf badIndexer)
                  <> ": "
                  <> T.pack (show badIndexer)

          _ ->
            throwEdh EvalError
              $  "Don't know how to index "
              <> T.pack (edhTypeNameOf tgtVal)
              <> ": "
              <> T.pack (show tgtVal)
              <> " with "
              <> T.pack (edhTypeNameOf ixVal)
              <> ": "
              <> T.pack (show ixVal)


    CallExpr procExpr argsSndr ->
      evalExpr procExpr $ \(OriginalValue callee'val _ callee'that) ->
        contEdhSTM
          $ edhMakeCall pgs callee'val callee'that argsSndr
          $ \mkCall -> runEdhProg pgs (mkCall exit)


    InfixExpr !opSym !lhExpr !rhExpr ->
      contEdhSTM $ resolveEdhCtxAttr pgs scope (AttrByName opSym) >>= \case
        Nothing ->
          throwEdhSTM pgs EvalError
            $  "Operator ("
            <> T.pack (show opSym)
            <> ") not in scope"
        Just (!opVal, !op'lexi) -> case opVal of

          -- calling an intrinsic operator
          EdhIntrOp _ (IntrinOpDefi _ _ iop'proc) ->
            runEdhProg pgs $ iop'proc lhExpr rhExpr exit

          -- calling an operator procedure
          EdhOprtor _ !op'pred !op'proc ->
            case procedure'args $ procedure'decl op'proc of
              -- 2 pos-args - simple lh/rh value receiving operator
              (PackReceiver [RecvArg{}, RecvArg{}]) ->
                runEdhProg pgs
                  $ evalExpr lhExpr
                  $ \(OriginalValue lhVal _ _) ->
                      evalExpr rhExpr $ \(OriginalValue rhVal _ _) ->
                        callEdhOperator (thatObject op'lexi)
                                        op'proc
                                        op'pred
                                        [lhVal, rhVal]
                                        exit
              -- 3 pos-args - caller scope + lh/rh expr receiving operator
              (PackReceiver [RecvArg{}, RecvArg{}, RecvArg{}]) -> do
                lhXV         <- edhExpr lhExpr
                rhXV         <- edhExpr rhExpr
                scopeWrapper <- mkScopeWrapper ctx scope
                runEdhProg pgs $ callEdhOperator
                  (thatObject op'lexi)
                  op'proc
                  op'pred
                  [EdhObject scopeWrapper, lhXV, rhXV]
                  exit
              _ ->
                throwEdhSTM pgs EvalError
                  $  "Invalid operator signature: "
                  <> T.pack (show $ procedure'args $ procedure'decl op'proc)

          _ ->
            throwEdhSTM pgs EvalError
              $  "Not callable "
              <> T.pack (edhTypeNameOf opVal)
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
  :: Expr
  -> AttrKey
  -> (EdhValue -> EdhProg (STM ()))
  -> EdhProcExit
  -> EdhProg (STM ())
getEdhAttr !fromExpr !key !exitNoAttr !exit = do
  !pgs <- ask
  let ctx          = edh'context pgs
      scope        = contextScope ctx
      this         = thisObject scope
      that         = thatObject scope
      thisObjScope = objectScope ctx this
  case fromExpr of
    -- give super objects the magical power to intercept
    -- attribute access on descendant objects, via `this` ref
    AttrExpr ThisRef ->
      let noMagic :: EdhProg (STM ())
          noMagic = contEdhSTM $ lookupEdhObjAttr pgs this key >>= \case
            EdhNil -> runEdhProg pgs $ exitNoAttr $ EdhObject this
            !val   -> exitEdhSTM' pgs exit $ OriginalValue val thisObjScope this
      in  getEdhAttrWithMagic (AttrByName "@<-") this key noMagic exit
    -- no magic layer laid over access via `that` ref
    AttrExpr ThatRef -> contEdhSTM $ lookupEdhObjAttr pgs that key >>= \case
      EdhNil -> runEdhProg pgs $ exitNoAttr $ EdhObject that
      !val   -> exitEdhSTM' pgs exit $ OriginalValue val thisObjScope that
    -- give super objects of an super object the metamagical power to
    -- intercept attribute access on super object, via `super` ref
    AttrExpr SuperRef ->
      let noMagic :: EdhProg (STM ())
          noMagic = contEdhSTM $ lookupEdhSuperAttr pgs this key >>= \case
            EdhNil -> runEdhProg pgs $ exitNoAttr $ EdhObject this
            !val   -> exitEdhSTM' pgs exit $ OriginalValue val thisObjScope this
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
        let fromScope = objectScope ctx obj
            noMagic :: EdhProg (STM ())
            noMagic = contEdhSTM $ lookupEdhObjAttr pgs obj key >>= \case
              EdhNil -> runEdhProg pgs $ exitNoAttr fromVal
              !val   -> exitEdhSTM' pgs exit $ OriginalValue val fromScope obj
        getEdhAttrWithMagic (AttrByName "@<-*") obj key noMagic exit
      _ -> contEdhSTM $ runEdhProg pgs $ exitNoAttr fromVal


-- There're 2 tiers of magic happen during object attribute resolution in Edh.
--  *) a magical super controls its direct descendants in behaving as an object, by
--     intercepting the attr resolution
--  *) a metamagical super controls its direct descendants in behaving as a magical
--     super, by intercepting the magic method (as attr) resolution

edhMetaMagicSpell :: AttrKey
edhMetaMagicSpell = AttrByName "!<-"

getEdhAttrWithMagic
  :: AttrKey
  -> Object
  -> AttrKey
  -> EdhProg (STM ())
  -> EdhProcExit
  -> EdhProg (STM ())
getEdhAttrWithMagic !magicSpell !obj !key !exitNoMagic !exit = do
  !pgs <- ask
  let
    ctx = edh'context pgs
    getViaSupers :: [Object] -> EdhProg (STM ())
    getViaSupers [] = exitNoMagic
    getViaSupers (super : restSupers) =
      getEdhAttrWithMagic edhMetaMagicSpell super magicSpell noMetamagic
        $ \(OriginalValue !magicVal !magicScope _) ->
            case edhUltimate magicVal of
              EdhMethod magicMth ->
                contEdhSTM $ withMagicMethod magicScope magicMth
              _ -> throwEdh EvalError $ "Invalid magic method type: " <> T.pack
                (edhTypeNameOf magicVal)
     where
      superScope = objectScope ctx super
      noMetamagic :: EdhProg (STM ())
      noMetamagic =
        contEdhSTM
          $   edhUltimate
          <$> lookupEdhObjAttr pgs super magicSpell
          >>= \case
                EdhNil              -> runEdhProg pgs $ getViaSupers restSupers
                EdhMethod !magicMth -> withMagicMethod superScope magicMth
                magicVal ->
                  throwEdhSTM pgs EvalError
                    $  "Invalid magic method type: "
                    <> T.pack (edhTypeNameOf magicVal)
      withMagicMethod :: Scope -> ProcDefi -> STM ()
      withMagicMethod !magicScope !magicMth =
        runEdhProg pgs
          $ callEdhMethod obj magicMth (ArgsPack [attrKeyValue key] Map.empty)
          $ \(OriginalValue !magicRtn _ _) -> case magicRtn of
              EdhContinue -> getViaSupers restSupers
              _ -> exitEdhProc' exit $ OriginalValue magicRtn magicScope obj
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
setEdhAttrWithMagic !pgsAfter !magicSpell !obj !key !val !exitNoMagic !exit =
  do
    !pgs <- ask
    contEdhSTM $ readTVar (objSupers obj) >>= runEdhProg pgs . setViaSupers
 where
  setViaSupers :: [Object] -> EdhProg (STM ())
  setViaSupers []                   = exitNoMagic
  setViaSupers (super : restSupers) = do
    !pgs <- ask
    let
      noMetamagic :: EdhProg (STM ())
      noMetamagic =
        contEdhSTM
          $   edhUltimate
          <$> lookupEdhObjAttr pgs super magicSpell
          >>= \case
                EdhNil              -> runEdhProg pgs $ setViaSupers restSupers
                EdhMethod !magicMth -> withMagicMethod magicMth
                magicVal ->
                  throwEdhSTM pgs EvalError
                    $  "Invalid magic method type: "
                    <> T.pack (edhTypeNameOf magicVal)
      withMagicMethod :: ProcDefi -> STM ()
      withMagicMethod !magicMth =
        runEdhProg pgs
          $ callEdhMethod obj
                          magicMth
                          (ArgsPack [attrKeyValue key, val] Map.empty)
          $ \(OriginalValue !magicRtn _ _) -> case magicRtn of
              EdhContinue -> setViaSupers restSupers
              _           -> local (const pgsAfter) $ exitEdhProc exit magicRtn
    getEdhAttrWithMagic edhMetaMagicSpell super magicSpell noMetamagic
      $ \(OriginalValue !magicVal _ _) -> case edhUltimate magicVal of
          EdhMethod !magicMth -> contEdhSTM $ withMagicMethod magicMth
          _ -> throwEdh EvalError $ "Invalid magic method type: " <> T.pack
            (edhTypeNameOf magicVal)


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
            changeEntityAttr pgs (objEntity this) key val
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
      changeEntityAttr pgs (objEntity that) key val
      runEdhProg pgsAfter $ exitEdhProc exit val
    -- not allowing assignment via super
    AttrExpr SuperRef -> throwEdh EvalError "Can not assign via super"
    -- give super objects the magical power to intercept
    -- attribute assignment to descendant objects, via obj ref
    _                 -> evalExpr tgtExpr $ \(OriginalValue !tgtVal _ _) ->
      case edhUltimate tgtVal of
        EdhObject !tgtObj ->
          let noMagic :: EdhProg (STM ())
              noMagic = contEdhSTM $ do
                changeEntityAttr pgs (objEntity tgtObj) key val
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
            <> T.pack (edhTypeNameOf tgtVal)
            <> ": "
            <> T.pack (show tgtVal)


edhMakeCall
  :: EdhProgState
  -> EdhValue
  -> Object
  -> ArgsSender
  -> ((EdhProcExit -> EdhProg (STM ())) -> STM ())
  -> STM ()
edhMakeCall !pgsCaller !callee'val !callee'that !argsSndr !callMaker =
  case callee'val of

    -- calling a class (constructor) procedure
    EdhClass !cls -> runEdhProg pgsCaller $ packEdhArgs argsSndr $ \apk ->
      contEdhSTM $ callMaker $ \exit -> constructEdhObject cls apk exit

    -- calling a method procedure
    EdhMethod !mth'proc ->
      runEdhProg pgsCaller $ packEdhArgs argsSndr $ \apk ->
        contEdhSTM $ callMaker $ \exit ->
          callEdhMethod callee'that mth'proc apk exit

    -- calling an interpreter procedure
    EdhIntrpr !mth'proc ->
      runEdhProg pgsCaller
        $ packEdhExprs argsSndr
        $ \apk@(ArgsPack args kwargs) -> contEdhSTM $ do
            -- an Edh interpreter proc needs a `callerScope` as its 1st arg,
            -- while a host interpreter proc doesn't.
            apk' <- case procedure'body $ procedure'decl mth'proc of
              Right _ -> return apk
              Left  _ -> do
                let callerCtx = edh'context pgsCaller
                !argCallerScope <- mkScopeWrapper callerCtx
                  $ contextScope callerCtx
                return $ ArgsPack (EdhObject argCallerScope : args) kwargs
            callMaker $ \exit -> callEdhMethod callee'that mth'proc apk' exit

    -- calling a producer procedure
    EdhPrducr !mth'proc -> case procedure'body $ procedure'decl mth'proc of
      Right _ -> throwEdhSTM pgsCaller EvalError "bug: host producer procedure"
      Left !pb ->
        runEdhProg pgsCaller
          $ packEdhArgs argsSndr
          $ \(ArgsPack !args !kwargs) -> contEdhSTM $ do
              (outlet, kwargs') <- case Map.lookup "outlet" kwargs of
                Nothing -> do
                  sink <- newEventSink
                  return (sink, Map.insert "outlet" (EdhSink sink) kwargs)
                Just (EdhSink !sink) -> return (sink, kwargs)
                Just !badVal ->
                  throwEdhSTM pgsCaller EvalError
                    $ "What's passed to a producer procedure as `outlet` is not a sink but a "
                    <> T.pack (edhTypeNameOf badVal)
              callMaker $ \exit ->
                launchEventProducer exit outlet $ callEdhMethod'
                  Nothing
                  callee'that
                  mth'proc
                  pb
                  (ArgsPack args kwargs')
                  edhEndOfProc

    -- calling a generator
    (EdhGnrtor _) -> throwEdhSTM
      pgsCaller
      EvalError
      "Can only call a generator method by for-from-do"

    _ ->
      throwEdhSTM pgsCaller EvalError
        $  "Can not call a "
        <> T.pack (edhTypeNameOf callee'val)
        <> ": "
        <> T.pack (show callee'val)


-- | Construct an Edh object from a class
constructEdhObject :: Class -> ArgsPack -> EdhProcExit -> EdhProg (STM ())
constructEdhObject !cls apk@(ArgsPack !args !kwargs) !exit = do
  pgsCaller <- ask
  createEdhObject cls apk $ \(OriginalValue !thisVal _ _) -> case thisVal of
    EdhObject !this -> do
      let thisEnt     = objEntity this
          callerCtx   = edh'context pgsCaller
          callerScope = contextScope callerCtx
          initScope   = callerScope { thisObject  = this
                                    , thatObject  = this
                                    , scopeProc   = cls
                                    , scopeCaller = contextStmt callerCtx
                                    }
          ctorCtx = callerCtx { callStack = initScope <| callStack callerCtx }
          pgsCtor = pgsCaller { edh'context = ctorCtx }
      contEdhSTM
        $   lookupEntityAttr pgsCtor thisEnt (AttrByName "__init__")
        >>= \case
              EdhNil -> if null args && Map.null kwargs
                then exitEdhSTM pgsCaller exit thisVal
                else
                  throwEdhSTM pgsCaller EvalError
                  $  "No __init__() defined by class "
                  <> procedure'name (procedure'decl cls)
                  <> " to receive argument(s)"
              EdhMethod !initMth ->
                case procedure'body $ procedure'decl initMth of
                  Right !hp ->
                    runEdhProg pgsCtor
                      $ hp apk
                      $ \(OriginalValue !hostInitRtn _ _) ->
                          -- a host __init__() method is responsible to return new
                          -- `this` explicitly, or another value as appropriate
                          contEdhSTM $ exitEdhSTM pgsCaller exit hostInitRtn
                  Left !pb ->
                    runEdhProg pgsCaller
                      $ local (const pgsCtor)
                      $ callEdhMethod' Nothing this initMth pb apk
                      $ \(OriginalValue !initRtn _ _) ->
                          local (const pgsCaller) $ case initRtn of
                              -- allow a __init__() procedure to explicitly return other
                              -- value than newly constructed `this` object
                              -- it can still `return this` to early stop the proc
                              -- which is magically an advanced feature
                            EdhReturn !rtnVal -> exitEdhProc exit rtnVal
                            EdhContinue       -> throwEdh
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
                throwEdhSTM pgsCaller EvalError
                  $  "Invalid __init__() method type from class - "
                  <> T.pack (edhTypeNameOf badInitMth)
    _ -> -- return whatever the constructor returned if not an object
      exitEdhProc exit thisVal

-- | Creating an Edh object from a class, without calling its `__init__()` method
createEdhObject :: Class -> ArgsPack -> EdhProcExit -> EdhProg (STM ())
createEdhObject !cls !apk !exit = do
  pgsCaller <- ask
  let !callerCtx   = edh'context pgsCaller
      !callerScope = contextScope callerCtx
  case procedure'body $ procedure'decl cls of

    -- calling a host class (constructor) procedure
    Right !hp -> contEdhSTM $ do
      -- note: cross check logic here with `mkHostClass`
      -- the host ctor procedure is responsible for instance creation, so the
      -- scope entiy, `this` and `that` are not changed for its call frame
      let !calleeScope =
            callerScope { scopeProc = cls, scopeCaller = contextStmt callerCtx }
          !calleeCtx = callerCtx
            { callStack       = calleeScope <| callStack callerCtx
            , generatorCaller = Nothing
            , contextMatch    = true
            }
          !pgsCallee = pgsCaller { edh'context = calleeCtx }
      runEdhProg pgsCallee $ hp apk $ \(OriginalValue !val _ _) ->
        contEdhSTM $ exitEdhSTM pgsCaller exit val

    -- calling an Edh class (constructor) procedure
    Left !pb -> contEdhSTM $ do
      newEnt  <- createHashEntity Map.empty
      newThis <- viewAsEdhObject newEnt cls []
      let !ctorScope = objectScope callerCtx newThis
          !ctorCtx   = callerCtx { callStack = ctorScope <| callStack callerCtx
                                 , generatorCaller = Nothing
                                 , contextMatch    = true
                                 , contextStmt     = pb
                                 }
          !pgsCtor = pgsCaller { edh'context = ctorCtx }
      runEdhProg pgsCtor $ evalStmt pb $ \(OriginalValue !ctorRtn _ _) ->
        local (const pgsCaller) $ case ctorRtn of
          -- allow a class procedure to explicitly return other
          -- value than newly constructed `this` object
          -- it can still `return this` to early stop the proc
          -- which is magically an advanced feature
          EdhReturn !rtnVal -> exitEdhProc exit rtnVal
          EdhContinue ->
            throwEdh EvalError "Unexpected continue from constructor"
          -- allow the use of `break` to early stop a constructor 
          -- procedure with nil result
          EdhBreak -> exitEdhProc exit nil
          -- no explicit return from class procedure, return the
          -- newly constructed this object, throw away the last
          -- value from the procedure execution
          _        -> exitEdhProc exit (EdhObject newThis)


callEdhOperator
  :: Object
  -> ProcDefi
  -> Maybe EdhValue
  -> [EdhValue]
  -> EdhProcExit
  -> EdhProg (STM ())
callEdhOperator !mth'that !mth'proc !prede !args !exit = do
  pgsCaller <- ask
  let callerCtx   = edh'context pgsCaller
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
                                                , scopeCaller = contextStmt
                                                  callerCtx
                                                }
          !mthCtx = callerCtx { callStack = mthScope <| callStack callerCtx
                              , generatorCaller = Nothing
                              , contextMatch = true
                              }
          !pgsMth = pgsCaller { edh'context = mthCtx }
      -- push stack for the host procedure
      local (const pgsMth)
        $ hp (ArgsPack args Map.empty)
        $ \(OriginalValue !val _ _) ->
        -- pop stack after host procedure returned
        -- return whatever the result a host procedure returned
            contEdhSTM $ exitEdhSTM pgsCaller exit val

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
  -> EdhProcExit
  -> EdhProg (STM ())
callEdhOperator' !gnr'caller !callee'that !mth'proc !prede !mth'body !args !exit
  = do
    !pgsCaller <- ask
    let !callerCtx = edh'context pgsCaller
        !recvCtx   = callerCtx { callStack       = lexicalScopeOf mth'proc :| []
                               , generatorCaller = Nothing
                               , contextMatch    = true
                               , contextStmt     = mth'body
                               }
    recvEdhArgs recvCtx
                (procedure'args $ procedure'decl mth'proc)
                (ArgsPack args Map.empty)
      $ \ed -> contEdhSTM $ do
          ent <- createHashEntity ed
          let !mthScope = (lexicalScopeOf mth'proc) { scopeEntity = ent
                                                    , thatObject  = callee'that
                                                    , scopeProc   = mth'proc
                                                    , scopeCaller = contextStmt
                                                      callerCtx
                                                    }
              !mthCtx = callerCtx { callStack = mthScope <| callStack callerCtx
                                  , generatorCaller = gnr'caller
                                  , contextMatch    = true
                                  , contextStmt     = mth'body
                                  }
              !pgsMth = pgsCaller { edh'context = mthCtx }
          case prede of
            Nothing      -> pure ()
            -- put the overridden predecessor operator in scope of the overriding
            -- op proc's run ctx
            Just !predOp -> changeEntityAttr
              pgsMth
              ent
              (AttrByName $ procedure'name $ procedure'decl mth'proc)
              predOp
          -- push stack for the Edh procedure
          runEdhProg pgsMth
            $ evalStmt mth'body
            $ \(OriginalValue !mthRtn _ _) ->
            -- pop stack after Edh procedure returned
                local (const pgsCaller) $ exitEdhProc exit mthRtn


callEdhMethod
  :: Object -> ProcDefi -> ArgsPack -> EdhProcExit -> EdhProg (STM ())
callEdhMethod !mth'that !mth'proc !apk !exit = do
  pgsCaller <- ask
  let callerCtx   = edh'context pgsCaller
      callerScope = contextScope callerCtx
  case procedure'body $ procedure'decl mth'proc of

    -- calling a host method procedure
    Right !hp -> do
      -- a host procedure views the same scope entity as of the caller's
      -- call frame
      let !mthScope = (lexicalScopeOf mth'proc) { scopeEntity = scopeEntity
                                                  callerScope
                                                , thatObject  = mth'that
                                                , scopeProc   = mth'proc
                                                , scopeCaller = contextStmt
                                                  callerCtx
                                                }
          !mthCtx = callerCtx { callStack = mthScope <| callStack callerCtx
                              , generatorCaller = Nothing
                              , contextMatch = true
                              }
          !pgsMth = pgsCaller { edh'context = mthCtx }
      -- push stack for the host procedure
      local (const pgsMth) $ hp apk $ \(OriginalValue !val _ _) ->
        -- pop stack after host procedure returned
        -- return whatever the result a host procedure returned
        contEdhSTM $ exitEdhSTM pgsCaller exit val

    -- calling an Edh method procedure
    Left !pb ->
      callEdhMethod' Nothing mth'that mth'proc pb apk
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
  -> EdhProcExit
  -> EdhProg (STM ())
callEdhMethod' !gnr'caller !callee'that !mth'proc !mth'body !apk !exit = do
  !pgsCaller <- ask
  let !callerCtx = edh'context pgsCaller
      !recvCtx   = callerCtx { callStack       = lexicalScopeOf mth'proc :| []
                             , generatorCaller = Nothing
                             , contextMatch    = true
                             , contextStmt     = mth'body
                             }
  recvEdhArgs recvCtx (procedure'args $ procedure'decl mth'proc) apk $ \ed ->
    contEdhSTM $ do
      ent <- createHashEntity ed
      let !mthScope = (lexicalScopeOf mth'proc) { scopeEntity = ent
                                                , thatObject  = callee'that
                                                , scopeProc   = mth'proc
                                                , scopeCaller = contextStmt
                                                  callerCtx
                                                }
          !mthCtx = callerCtx { callStack = mthScope <| callStack callerCtx
                              , generatorCaller = gnr'caller
                              , contextMatch    = true
                              , contextStmt     = mth'body
                              }
          !pgsMth = pgsCaller { edh'context = mthCtx }
      -- push stack for the Edh procedure
      runEdhProg pgsMth $ evalStmt mth'body $ \(OriginalValue !mthRtn _ _) ->
        -- pop stack after Edh procedure returned
        local (const pgsCaller) $ exitEdhProc exit mthRtn


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
            EdhNil -> -- nil yielded from a generator effectively early stops
              exitEdhProc exit nil
            _ ->
              recvEdhArgs
                  ctx
                  argsRcvr
                  (case yielded'val of
                    EdhArgsPack apk -> apk
                    _               -> ArgsPack [yielded'val] Map.empty
                  )
                $ \em -> contEdhSTM $ do
                    updateEntityAttrs pgs (scopeEntity scope) $ Map.toList em
                    runEdhProg pgs
                      $ evalExpr doExpr
                      $ \(OriginalValue !doResult _ _) -> case doResult of
                          EdhContinue ->
                            -- propagate the continue to generator
                            contEdhSTM $ genrCont EdhContinue
                          EdhBreak ->
                            -- break out of the for-from-do loop
                            exitEdhProc exit nil
                          EdhReturn !rtnVal ->
                            -- early return from for-from-do
                            exitEdhProc exit (EdhReturn rtnVal)
                          _ -> contEdhSTM $ do
                            -- normal result from do, send to generator
                            iterCollector doResult
                            genrCont doResult

    runEdhProg pgsLooper $ case deParen iterExpr of
      CallExpr !procExpr !argsSndr -> -- loop over a generator
        evalExpr procExpr
          $ \(OriginalValue !callee'val !_callee'scope !callee'that) ->
              case callee'val of

                -- calling a generator
                (EdhGnrtor !gnr'proc) -> packEdhArgs argsSndr $ \apk ->
                  case procedure'body $ procedure'decl gnr'proc of

                    -- calling a host generator
                    Right !hp -> contEdhSTM $ forLooper $ \exit -> do
                      pgs <- ask
                      let !ctx   = edh'context pgs
                          !scope = contextScope ctx
                      contEdhSTM $ do
                        -- a host procedure views the same scope entity as of the caller's
                        -- call frame
                        let !calleeScope = (lexicalScopeOf gnr'proc)
                              { scopeEntity = scopeEntity scope
                              , thatObject  = callee'that
                              , scopeProc   = gnr'proc
                              , scopeCaller = contextStmt ctx
                              }
                            !calleeCtx = ctx
                              { callStack       = calleeScope <| callStack ctx
                              , generatorCaller = Just (pgs, recvYield exit)
                              , contextMatch    = true
                              }
                            !pgsCallee = pgs { edh'context = calleeCtx }
                        -- insert a cycle tick here, so if no tx required for the call
                        -- overall, the callee resolution tx stops here then the callee
                        -- runs in next stm transaction
                        flip (exitEdhSTM' pgsCallee) (wuji pgsCallee) $ \_ ->
                          hp apk $ \(OriginalValue val _ _) ->
                            -- return the result in CPS with caller pgs restored
                            contEdhSTM $ exitEdhSTM pgsLooper exit val

                    -- calling an Edh generator
                    Left !pb -> contEdhSTM $ forLooper $ \exit -> do
                      pgs <- ask
                      callEdhMethod' (Just (pgs, recvYield exit))
                                     callee'that
                                     gnr'proc
                                     pb
                                     apk
                        $ \(OriginalValue !val _ _) ->
                            -- return the result in CPS with looper pgs restored
                            contEdhSTM $ exitEdhSTM pgsLooper exit val

                -- calling other procedures, assume to loop over its return value
                _ ->
                  contEdhSTM
                    $ edhMakeCall pgsLooper callee'val callee'that argsSndr
                    $ \mkCall ->
                        runEdhProg pgsLooper
                          $ mkCall
                          $ \(OriginalValue !iterVal _ _) ->
                              loopOverValue iterVal

      _ -> -- loop over an iterable value
           evalExpr iterExpr
        $ \(OriginalValue !iterVal _ _) -> loopOverValue iterVal

 where

  loopOverValue :: EdhValue -> EdhProg (STM ())
  loopOverValue !iterVal = contEdhSTM $ forLooper $ \exit -> do
    pgs <- ask
    let !ctx   = edh'context pgs
        !scope = contextScope ctx
    contEdhSTM $ do
      let -- do one iteration
          do1 :: ArgsPack -> STM () -> STM ()
          do1 !apk !next =
            runEdhProg pgs $ recvEdhArgs ctx argsRcvr apk $ \em ->
              contEdhSTM $ do
                updateEntityAttrs pgs (scopeEntity scope) $ Map.toList em
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
            EdhNil -> -- nil marks end-of-stream from an event sink
              exitEdhSTM pgs exit nil -- stop the for-from-do loop
            EdhArgsPack apk -> do1 apk $ iterEvt subChan
            v               -> do1 (ArgsPack [v] Map.empty) $ iterEvt subChan

      case iterVal of

        -- loop from an event sink
        (EdhSink sink) -> subscribeEvents sink >>= \(subChan, mrv) ->
          case mrv of
            Nothing -> iterEvt subChan
            Just ev -> case ev of
              EdhNil -> -- this sink is already marked at end-of-stream
                exitEdhSTM pgs exit nil
              EdhArgsPack apk -> do1 apk $ iterEvt subChan
              v               -> do1 (ArgsPack [v] Map.empty) $ iterEvt subChan

        -- loop from a positonal-only args pack
        (EdhArgsPack (ArgsPack !args !kwargs)) | Map.null kwargs -> iterThem
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
        (EdhList (List _ !l)) -> do
          ll <- readTVar l
          iterThem
            [ case val of
                EdhArgsPack apk' -> apk'
                _                -> ArgsPack [val] Map.empty
            | val <- ll
            ]

        -- loop from a dict
        (EdhDict (Dict _ !d)) -> do
          ds <- readTVar d
          -- don't be tempted to yield pairs from a dict here,
          -- it'll be messy if some entry values are themselves pairs
          iterThem [ ArgsPack [k, v] Map.empty | (k, v) <- Map.toList ds ]

        -- TODO define the magic method for an object to be able to respond
        --      to for-from-do looping

        _ ->
          throwEdhSTM pgsLooper EvalError
            $  "Can not do a for loop from "
            <> T.pack (edhTypeNameOf iterVal)
            <> ": "
            <> T.pack (show iterVal)


-- | Create a reflective object capturing the specified scope as from the
-- specified context
--
-- the contextStmt is captured as the procedure body of its fake class
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
    , procedure'decl = ProcDecl { procedure'name = "<captured-scope>"
                                , procedure'args = PackReceiver []
                                , procedure'body = Left $ contextStmt ctx
                                }
    }

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
      DirectRef !addr' ->
        contEdhSTM $ resolveEdhAttrAddr pgs addr' >>= \key -> do
          changeEntityAttr pgs
                           (scopeEntity $ contextScope $ edh'context pgs)
                           key
                           rhVal
          runEdhProg pgsAfter $ exitEdhProc exit rhVal
      -- assign to an addressed attribute
      IndirectRef !tgtExpr !addr' -> contEdhSTM $ do
        key <- resolveEdhAttrAddr pgs addr'
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
          throwEdh EvalError $ "Invalid attribute reference type - " <> T.pack
            (show $ edhTypeOf addrVal)
    x ->
      throwEdh EvalError
        $  "Invalid left hand expression for assignment: "
        <> T.pack (show x)


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
  -> (Map.HashMap AttrKey EdhValue -> EdhProg (STM ()))
  -> EdhProg (STM ())
recvEdhArgs !recvCtx !argsRcvr apk@(ArgsPack !posArgs !kwArgs) !exit = do
  !pgsCaller <- ask
  let -- args receive always done in callee's context with tx on
    !pgsRecv = pgsCaller { edh'in'tx = True, edh'context = recvCtx }
    recvFromPack
      :: (ArgsPack, Map.HashMap AttrKey EdhValue)
      -> ArgReceiver
      -> STM (ArgsPack, Map.HashMap AttrKey EdhValue)
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
              $ assignEdhTarget pgsCaller (AttrExpr addr) edhEndOfProc argVal
            return (ArgsPack posArgs'' kwArgs'', em)
          tgt ->
            throwEdhSTM pgsRecv EvalError
              $  "Invalid argument retarget: "
              <> T.pack (show tgt)
     where
      resolveArgValue
        :: AttrName
        -> Maybe Expr
        -> STM (EdhValue, [EdhValue], Map.HashMap AttrName EdhValue)
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
                  (\(OriginalValue !val _ _) ->
                    contEdhSTM (putTMVar defaultVar val)
                  )
                defaultVal <- readTMVar defaultVar
                return (defaultVal, posArgs', kwArgs'')
              _ ->
                throwEdhSTM pgsCaller EvalError
                  $  "Missing argument: "
                  <> argName
    woResidual
      :: ArgsPack
      -> Map.HashMap AttrKey EdhValue
      -> STM (Map.HashMap AttrKey EdhValue)
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
      = return em
    doReturn :: Map.HashMap AttrKey EdhValue -> STM ()
    doReturn !es =
      -- insert a cycle tick here, so if no tx required for the call
      -- overall, the args receiving tx stops here then the callee
      -- runs in next stm transaction
      exitEdhSTM' pgsCaller (\_ -> exit es) (wuji pgsCaller)

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
      then doReturn
        (Map.fromList [ (AttrByName k, v) | (k, v) <- Map.toList kwArgs ])
      else
        throwEdhSTM pgsRecv EvalError
        $  "Unexpected "
        <> T.pack (show $ length posArgs)
        <> " positional argument(s) to wild receiver"


-- | Pack args as expressions, normally in preparation of calling another
-- interpreter procedure
packEdhExprs :: ArgsSender -> (ArgsPack -> EdhProg (STM ())) -> EdhProg (STM ())
packEdhExprs []       !exit = exit (ArgsPack [] Map.empty)
packEdhExprs (x : xs) !exit = case x of
  UnpackPosArgs _ -> throwEdh EvalError "unpack to expr not supported yet"
  UnpackKwArgs _ -> throwEdh EvalError "unpack to expr not supported yet"
  UnpackPkArgs _ -> throwEdh EvalError "unpack to expr not supported yet"
  SendPosArg !argExpr -> packEdhExprs xs $ \(ArgsPack !posArgs !kwArgs) -> do
    pgs <- ask
    contEdhSTM $ do
      xv <- edhExpr argExpr
      runEdhProg pgs $ exit (ArgsPack (xv : posArgs) kwArgs)
  SendKwArg !kw !argExpr -> do
    pgs <- ask
    contEdhSTM $ do
      xv <- edhExpr argExpr
      runEdhProg pgs $ packEdhExprs xs $ \(ArgsPack !posArgs !kwArgs) ->
        exit (ArgsPack posArgs $ Map.insert kw xv kwArgs)


-- | Pack args as caller, normally in preparation of calling another procedure
packEdhArgs :: ArgsSender -> (ArgsPack -> EdhProg (STM ())) -> EdhProg (STM ())
packEdhArgs !argsSender !pkExit = do
  !pgs <- ask
  -- make sure values in a pack are evaluated in same tx
  let !pgsPacking = pgs { edh'in'tx = True }
  local (const pgsPacking) $ pkArgs argsSender $ \apk ->
    -- restore original tx state after args packed
    local (const pgs) $ pkExit apk
 where
  pkArgs :: [ArgSender] -> (ArgsPack -> EdhProg (STM ())) -> EdhProg (STM ())
  pkArgs []       !exit = exit (ArgsPack [] Map.empty)
  pkArgs (x : xs) !exit = do
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
          EdhString !name -> return name
          k ->
            throwEdhSTM pgs EvalError
              $  "Invalid argument keyword from dict key: "
              <> T.pack (show k)
    case x of
      UnpackPosArgs !posExpr ->
        evalExpr posExpr $ \(OriginalValue !val _ _) -> case val of
          (EdhArgsPack (ArgsPack !posArgs' _kwArgs')) ->
            pkArgs xs $ \(ArgsPack !posArgs !kwArgs) ->
              exit (ArgsPack (posArgs ++ posArgs') kwArgs)
          (EdhPair !k !v) -> pkArgs xs $ \(ArgsPack !posArgs !kwArgs) ->
            exit (ArgsPack (posArgs ++ [k, v]) kwArgs)
          (EdhTuple !l) -> pkArgs xs $ \(ArgsPack !posArgs !kwArgs) ->
            exit (ArgsPack (posArgs ++ l) kwArgs)
          (EdhList (List _ !l)) -> pkArgs xs $ \(ArgsPack !posArgs !kwArgs) ->
            contEdhSTM $ do
              ll <- readTVar l
              runEdhProg pgs $ exit (ArgsPack (posArgs ++ ll) kwArgs)
          _ ->
            throwEdh EvalError
              $  "Can not unpack args from a "
              <> T.pack (edhTypeNameOf val)
              <> ": "
              <> T.pack (show val)
      UnpackKwArgs !kwExpr -> evalExpr kwExpr $ \(OriginalValue !val _ _) ->
        case val of
          EdhArgsPack (ArgsPack _posArgs' !kwArgs') ->
            pkArgs xs $ \(ArgsPack !posArgs !kwArgs) ->
              exit (ArgsPack posArgs (Map.union kwArgs kwArgs'))
          (EdhPair !k !v) -> pkArgs xs $ \case
            (ArgsPack !posArgs !kwArgs) -> contEdhSTM $ do
              kw <- edhVal2Kw k
              runEdhProg pgs $ exit (ArgsPack posArgs $ Map.insert kw v kwArgs)
          (EdhDict (Dict _ !ds)) -> pkArgs xs $ \case
            (ArgsPack !posArgs !kwArgs) -> contEdhSTM $ do
              dm  <- readTVar ds
              kvl <- forM (Map.toList dm) $ \(k, v) -> (, v) <$> dictKey2Kw k
              runEdhProg pgs $ exit
                (ArgsPack posArgs $ Map.union kwArgs $ Map.fromList kvl)
          _ ->
            throwEdh EvalError
              $  "Can not unpack kwargs from a "
              <> T.pack (edhTypeNameOf val)
              <> ": "
              <> T.pack (show val)
      UnpackPkArgs !pkExpr -> evalExpr pkExpr $ \(OriginalValue !val _ _) ->
        case val of
          (EdhArgsPack (ArgsPack !posArgs' !kwArgs')) -> pkArgs xs $ \case
            (ArgsPack !posArgs !kwArgs) ->
              exit (ArgsPack (posArgs ++ posArgs') (Map.union kwArgs kwArgs'))
          _ ->
            throwEdh EvalError
              $  "Can not unpack pkargs from a "
              <> T.pack (edhTypeNameOf val)
              <> ": "
              <> T.pack (show val)
      SendPosArg !argExpr -> evalExpr argExpr $ \(OriginalValue !val _ _) ->
        pkArgs xs $ \(ArgsPack !posArgs !kwArgs) ->
          exit (ArgsPack (val : posArgs) kwArgs)
      SendKwArg !kw !argExpr ->
        evalExpr argExpr $ \(OriginalValue !val _ _) ->
          pkArgs xs $ \pk@(ArgsPack !posArgs !kwArgs) -> case kw of
            "_" -> -- silently drop the value to keyword of single underscore
              exit pk -- the user may just want its side-effect
            _ -> exit
              (ArgsPack posArgs $ Map.alter
                (\case -- make sure latest value with same kw take effect
                  Nothing        -> Just val
                  Just !laterVal -> Just laterVal
                )
                kw
                kwArgs
              )


-- comma separated repr string
_edhCSR :: [Text] -> [EdhValue] -> EdhProcExit -> EdhProg (STM ())
_edhCSR reprs [] !exit =
  exitEdhProc exit $ EdhString $ T.concat [ i <> ", " | i <- reverse reprs ]
_edhCSR reprs (v : rest) !exit = edhValueRepr v $ \(OriginalValue r _ _) ->
  case r of
    EdhString repr -> _edhCSR (repr : reprs) rest exit
    _              -> error "bug: edhValueRepr returned non-string in CPS"
-- comma separated repr string for kwargs
_edhKwArgsCSR
  :: [(Text, Text)] -> [(Text, EdhValue)] -> EdhProcExit -> EdhProg (STM ())
_edhKwArgsCSR entries [] !exit' = exitEdhProc exit' $ EdhString $ T.concat
  [ k <> "=" <> v <> ", " | (k, v) <- reverse entries ]
_edhKwArgsCSR entries ((k, v) : rest) exit' =
  edhValueRepr v $ \(OriginalValue r _ _) -> case r of
    EdhString repr -> _edhKwArgsCSR ((k, repr) : entries) rest exit'
    _              -> error "bug: edhValueRepr returned non-string in CPS"
-- comma separated repr string for dict entries
_edhDictCSR
  :: [(Text, Text)] -> [(EdhValue, EdhValue)] -> EdhProcExit -> EdhProg (STM ())
_edhDictCSR entries [] !exit' = exitEdhProc exit' $ EdhString $ T.concat
  [ k <> ":" <> v <> ", " | (k, v) <- reverse entries ]
_edhDictCSR entries ((k, v) : rest) exit' =
  edhValueRepr k $ \(OriginalValue kr _ _) -> case kr of
    EdhString !kRepr -> do
      let vrDecor :: Text -> Text
          vrDecor = case v of
            -- quote the value repr in the entry if it's a pair
            EdhPair{} -> \r -> "(" <> r <> ")"
            _         -> id
      edhValueRepr v $ \(OriginalValue vr _ _) -> case vr of
        EdhString !vRepr ->
          _edhDictCSR ((kRepr, vrDecor vRepr) : entries) rest exit'
        _ -> error "bug: edhValueRepr returned non-string in CPS"
    _ -> error "bug: edhValueRepr returned non-string in CPS"

edhValueRepr :: EdhValue -> EdhProcExit -> EdhProg (STM ())

-- pair repr
edhValueRepr (EdhPair v1 v2) !exit =
  edhValueRepr v1 $ \(OriginalValue r1 _ _) -> case r1 of
    EdhString repr1 -> edhValueRepr v2 $ \(OriginalValue r2 _ _) -> case r2 of
      EdhString repr2 -> exitEdhProc exit $ EdhString $ repr1 <> ":" <> repr2
      _               -> error "bug: edhValueRepr returned non-string in CPS"
    _ -> error "bug: edhValueRepr returned non-string in CPS"

-- tuple repr
edhValueRepr (EdhTuple []) !exit = -- no space should show in an empty tuple
  exitEdhProc exit $ EdhString "()"
edhValueRepr (EdhTuple vs) !exit = _edhCSR [] vs $ \(OriginalValue csr _ _) ->
  case csr of
    -- advocate trailing comma here
    EdhString !csRepr -> exitEdhProc exit $ EdhString $ "( " <> csRepr <> ")"
    _                 -> error "bug: edhValueRepr returned non-string in CPS"

-- argspack repr
edhValueRepr (EdhArgsPack (ArgsPack !args !kwargs)) !exit
  | null args && Map.null kwargs = exitEdhProc exit $ EdhString "pkargs()"
  | otherwise = _edhCSR [] args $ \(OriginalValue argsR _ _) -> case argsR of
    EdhString argsCSR ->
      _edhKwArgsCSR [] (Map.toList kwargs) $ \(OriginalValue kwargsR _ _) ->
        case kwargsR of
          EdhString kwargsCSR ->
            exitEdhProc exit
              $  EdhString
              $  "pkargs( "
              <> argsCSR
              <> kwargsCSR
              <> ")"
          _ -> error "bug: edhValueRepr returned non-string in CPS"
    _ -> error "bug: edhValueRepr returned non-string in CPS"

-- list repr
edhValueRepr (EdhList (List _ ls)) !exit = do
  pgs <- ask
  contEdhSTM $ readTVar ls >>= \vs -> if null vs
    then -- no space should show in an empty list
         exitEdhSTM pgs exit $ EdhString "[]"
    else runEdhProg pgs $ _edhCSR [] vs $ \(OriginalValue csr _ _) ->
      case csr of
        -- advocate trailing comma here
        EdhString !csRepr ->
          exitEdhProc exit $ EdhString $ "[ " <> csRepr <> "]"
        _ -> error "bug: edhValueRepr returned non-string in CPS"

-- dict repr
edhValueRepr (EdhDict (Dict _ dsv)) !exit = do
  pgs <- ask
  contEdhSTM $ do
    ds <- readTVar dsv
    if Map.null ds
      then exitEdhSTM pgs exit $ EdhString "{}" -- no space should show in an empty dict
      else
        runEdhProg pgs
        $ _edhDictCSR [] (Map.toList ds)
        $ \(OriginalValue entriesR _ _) -> case entriesR of
            EdhString entriesCSR ->
              exitEdhProc exit $ EdhString $ "{ " <> entriesCSR <> "}"
            _ -> error "bug: edhValueRepr returned non-string in CPS"

-- object repr
edhValueRepr (EdhObject !o) !exit = do
  pgs <- ask
  contEdhSTM $ lookupEdhObjAttr pgs o (AttrByName "__repr__") >>= \case
    EdhNil -> exitEdhSTM pgs exit $ EdhString $ T.pack $ show o
    EdhMethod !reprMth ->
      runEdhProg pgs
        $ callEdhMethod o reprMth (ArgsPack [] Map.empty)
        $ \(OriginalValue reprVal _ _) -> case reprVal of
            s@EdhString{} -> exitEdhProc exit s
            _             -> edhValueRepr reprVal exit
    repr@EdhString{} -> exitEdhSTM pgs exit repr
    reprVal          -> runEdhProg pgs $ edhValueRepr reprVal exit

-- repr of named value
edhValueRepr (EdhNamedValue !n v@EdhNamedValue{}) !exit =
  -- Edh operators are all left-associative, parenthesis needed
  edhValueRepr v $ \(OriginalValue r _ _) -> case r of
    EdhString repr ->
      exitEdhProc exit $ EdhString $ n <> " := (" <> repr <> ")"
    _ -> error "bug: edhValueRepr returned non-string in CPS"
edhValueRepr (EdhNamedValue !n !v) !exit =
  edhValueRepr v $ \(OriginalValue r _ _) -> case r of
    EdhString repr -> exitEdhProc exit $ EdhString $ n <> " := " <> repr
    _              -> error "bug: edhValueRepr returned non-string in CPS"

-- repr of other values simply as to show itself
edhValueRepr !v !exit = exitEdhProc exit $ EdhString $ T.pack $ show v


data ArgsPackParser a = ArgsPackParser {
    pos'parsers :: [EdhValue -> a -> Either Text a]
    , kw'parsers :: Map.HashMap AttrName (EdhValue ->  a -> Either Text a)
  }
parseArgsPack :: a -> ArgsPackParser a -> ArgsPack -> Either Text a
parseArgsPack defVal (ArgsPackParser posParsers kwParsers) (ArgsPack posArgs kwArgs)
  = go posParsers kwParsers posArgs (Map.toList kwArgs) defVal
 where
  go
    :: [EdhValue -> a -> Either Text a]
    -> Map.HashMap AttrName (EdhValue -> a -> Either Text a)
    -> [EdhValue]
    -> [(AttrName, EdhValue)]
    -> a
    -> Either Text a
  go _  _    []      []                     result = Right result
  go [] _    (_ : _) _                      _      = Left "too many args"
  go _  kwps []      ((kwn, kwv) : kwargs') result = case Map.lookup kwn kwps of
    Nothing  -> Left $ "unknown arg: " <> kwn
    Just kwp -> kwp kwv result >>= go [] kwps [] kwargs'
  go (p : posParsers') kwps (arg : args') kwargs result =
    p arg result >>= go posParsers' kwps args' kwargs

