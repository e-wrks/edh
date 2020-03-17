
module Language.Edh.Batteries.Reflect where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.Reader
import           Control.Concurrent.STM

import           Data.List.NonEmpty             ( (<|) )
import qualified Data.List.NonEmpty            as NE
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

import           Language.Edh.Control
import           Language.Edh.Runtime


-- | utility constructor(*args,**kwargs)
ctorProc :: EdhProcedure
ctorProc !argsSender !exit = do
  !pgs <- ask
  let callerCtx   = edh'context pgs
      callerScope = contextScope callerCtx
  packEdhArgs argsSender $ \(ArgsPack !args !kwargs) ->
    let !argsCls = edhClassOf <$> args
    in  if null kwargs
          then case argsCls of
            [] ->
              exitEdhProc exit (EdhClass $ objClass $ thisObject callerScope)
            [t] -> exitEdhProc exit t
            _   -> exitEdhProc exit (EdhTuple argsCls)
          else exitEdhProc
            exit
            (EdhArgsPack $ ArgsPack argsCls $ Map.map edhClassOf kwargs)
 where
  edhClassOf :: EdhValue -> EdhValue
  edhClassOf (EdhObject o) = EdhClass $ objClass o
  edhClassOf _             = nil

-- | utility supers(*args,**kwargs)
supersProc :: EdhProcedure
supersProc !argsSender !exit = do
  !pgs <- ask
  let !callerCtx   = edh'context pgs
      !callerScope = contextScope callerCtx
      !argCnt      = length argsSender
  if argCnt < 1
    then contEdhSTM $ do
      supers <-
        map EdhObject <$> (readTVar $ objSupers $ thatObject callerScope)
      exitEdhSTM pgs exit (EdhTuple supers)
    else packEdhArgs argsSender $ \(ArgsPack !args !kwargs) -> if null kwargs
      then case args of
        [v] -> contEdhSTM $ do
          supers <- supersOf v
          exitEdhSTM pgs exit supers
        _ -> contEdhSTM $ do
          argsSupers <- sequence $ supersOf <$> args
          exitEdhSTM pgs exit (EdhTuple argsSupers)
      else contEdhSTM $ do
        argsSupers   <- sequence $ supersOf <$> args
        kwargsSupers <- sequence $ Map.map supersOf kwargs
        exitEdhSTM pgs exit (EdhArgsPack $ ArgsPack argsSupers kwargsSupers)
 where
  supersOf :: EdhValue -> STM EdhValue
  supersOf v = case v of
    EdhObject o ->
      map EdhObject <$> readTVar (objSupers o) >>= return . EdhTuple
    _ -> return nil


-- | utility scope()
-- obtain current scope as reflected object
scopeObtainProc :: EdhProcedure
scopeObtainProc _ !exit = do
  !pgs <- ask
  let !ctx      = edh'context pgs
      !tgtScope = case NE.tail $ callStack ctx of
        -- a host proc has its own stack frame, should wrap the next frame
        (edhScope : _) -> edhScope
        _ -> error "bug: host procedure `scope()` called from nowhere"
  contEdhSTM $ do
    wrapperObj <- mkScopeWrapper (contextWorld ctx) tgtScope
    exitEdhSTM pgs exit $ EdhObject wrapperObj


-- | utility scope.attrs()
-- get attribute types in the scope
scopeAttrsProc :: EdhProcedure
scopeAttrsProc _ !exit = do
  !pgs <- ask
  let !that = thatObject $ contextScope $ edh'context pgs
  contEdhSTM $ do
    ad <- edhDictFromEntity pgs $ scopeEntity $ wrappedScopeOf that
    exitEdhSTM pgs exit $ EdhDict ad


-- | utility scope.lexiLoc()
-- get lexical source locations formated as a string, from the wrapped scope
scopeLexiLocProc :: EdhProcedure
scopeLexiLocProc _ !exit = do
  !pgs <- ask
  let !that = thatObject $ contextScope $ edh'context pgs
  exitEdhProc exit $ EdhString $ T.pack $ show $ wrappedScopeOf that


-- | utility scope.outer()
-- get lexical outer scope of the wrapped scope
scopeOuterProc :: EdhProcedure
scopeOuterProc _ !exit = do
  !pgs <- ask
  let !ctx  = edh'context pgs
      !that = thatObject $ contextScope ctx
  case outerScopeOf $ wrappedScopeOf that of
    Nothing     -> exitEdhProc exit nil
    Just !outer -> contEdhSTM $ do
      wrappedObj <- mkScopeWrapper (contextWorld ctx) outer
      exitEdhSTM pgs exit $ EdhObject wrappedObj


-- | utility scope.get(k1, k2, n1=k3, n2=k4, ...)
-- get attribute values from the wrapped scope
scopeGetProc :: EdhProcedure
scopeGetProc !argsSender !exit = do
  !pgs <- ask
  let !callerCtx = edh'context pgs
      !that      = thatObject $ contextScope callerCtx
      !ent       = scopeEntity $ wrappedScopeOf that
      lookupAttrs
        :: [EdhValue]
        -> [(AttrName, EdhValue)]
        -> [EdhValue]
        -> [(AttrName, EdhValue)]
        -> STM ([EdhValue], [(AttrName, EdhValue)])
      lookupAttrs rtnArgs rtnKwArgs [] [] = return (rtnArgs, rtnKwArgs)
      lookupAttrs rtnArgs rtnKwArgs [] ((n, v) : restKwArgs) = do
        k       <- attrKeyFrom pgs v
        attrVal <- lookupEntityAttr pgs ent k
        lookupAttrs rtnArgs ((n, attrVal) : rtnKwArgs) [] restKwArgs
      lookupAttrs rtnArgs rtnKwArgs (v : restArgs) kwargs = do
        k       <- attrKeyFrom pgs v
        attrVal <- lookupEntityAttr pgs ent k
        lookupAttrs (attrVal : rtnArgs) rtnKwArgs restArgs kwargs
  packEdhArgs argsSender $ \(ArgsPack !args !kwargs) ->
    contEdhSTM $ lookupAttrs [] [] args (Map.toList kwargs) >>= \case
      ([v]    , []       ) -> exitEdhSTM pgs exit v
      (rtnArgs, rtnKwArgs) -> exitEdhSTM pgs exit $ EdhArgsPack $ ArgsPack
        (reverse rtnArgs)
        (Map.fromList rtnKwArgs)
 where
  attrKeyFrom :: EdhProgState -> EdhValue -> STM AttrKey
  attrKeyFrom _ (EdhString attrName) = return $ AttrByName attrName
  attrKeyFrom _ (EdhSymbol sym     ) = return $ AttrBySym sym
  attrKeyFrom pgs badVal =
    throwEdhSTM pgs EvalError
      $  "Invalid attribute reference - "
      <> edhValueStr (edhTypeOf badVal)
      <> ": "
      <> edhValueStr badVal


-- | utility scope.put(k1:v1, k2:v2, n3=v3, n4=v4, ...)
-- put attribute values into the wrapped scope
scopePutProc :: EdhProcedure
scopePutProc !argsSender !exit = do
  !pgs <- ask
  let !callerCtx = edh'context pgs
      !that      = thatObject $ contextScope callerCtx
      !ent       = scopeEntity $ wrappedScopeOf that
  packEdhArgs argsSender $ \(ArgsPack !args !kwargs) -> contEdhSTM $ do
    attrs <- putAttrs pgs args []
    updateEntityAttrs pgs ent
      $  attrs
      ++ [ (AttrByName k, v) | (k, v) <- Map.toList kwargs ]
    exitEdhSTM pgs exit nil
 where
  putAttrs
    :: EdhProgState
    -> [EdhValue]
    -> [(AttrKey, EdhValue)]
    -> STM [(AttrKey, EdhValue)]
  putAttrs _   []           cumu = return cumu
  putAttrs pgs (arg : args) cumu = case arg of
    EdhPair (EdhString !k) !v  -> putAttrs pgs args ((AttrByName k, v) : cumu)
    EdhPair (EdhSymbol !k) !v  -> putAttrs pgs args ((AttrBySym k, v) : cumu)
    EdhTuple [EdhString !k, v] -> putAttrs pgs args ((AttrByName k, v) : cumu)
    EdhTuple [EdhSymbol !k, v] -> putAttrs pgs args ((AttrBySym k, v) : cumu)
    _ ->
      throwEdhSTM pgs EvalError
        $  "Invalid key/value spec to put into a scope - "
        <> edhValueStr (edhTypeOf arg)
        <> ": "
        <> edhValueStr arg


-- | utility scope.eval(expr1, expr2, kw3=expr3, kw4=expr4, ...)
-- evaluate expressions in this scope
scopeEvalProc :: EdhProcedure
scopeEvalProc !argsSender !exit = do
  !pgs <- ask
  let
    !callerCtx      = edh'context pgs
    !that           = thatObject $ contextScope callerCtx
    -- eval all exprs with the original scope as the only scope in call stack
    !scopeCallStack = wrappedScopeOf that <| callStack callerCtx
    evalThePack
      :: [EdhValue]
      -> Map.HashMap AttrName EdhValue
      -> [EdhValue]
      -> [(AttrName, EdhValue)]
      -> EdhProg (STM ())
    evalThePack !argsValues !kwargsValues [] [] =
      contEdhSTM
        -- restore original program state and return the eval-ed values
        $ exitEdhSTM pgs exit
        $ case argsValues of
            [val] | null kwargsValues -> val
            _ -> EdhArgsPack $ ArgsPack (reverse argsValues) kwargsValues
    evalThePack !argsValues !kwargsValues [] (kwExpr : kwargsExprs') =
      case kwExpr of
        (!kw, EdhExpr _ !expr _) ->
          evalExpr expr $ \(OriginalValue !val _ _) -> evalThePack
            argsValues
            (Map.insert kw val kwargsValues)
            []
            kwargsExprs'
        v -> throwEdh EvalError $ "Not an expr: " <> T.pack (show v)
    evalThePack !argsValues !kwargsValues (!argExpr : argsExprs') !kwargsExprs
      = case argExpr of
        EdhExpr _ !expr _ -> evalExpr expr $ \(OriginalValue !val _ _) ->
          evalThePack (val : argsValues) kwargsValues argsExprs' kwargsExprs
        v -> throwEdh EvalError $ "Not an expr: " <> T.pack (show v)
  packEdhArgs argsSender $ \(ArgsPack !args !kwargs) ->
    if null kwargs && null args
      then exitEdhProc exit nil
      else
        contEdhSTM
        $ runEdhProg pgs
            { edh'context = callerCtx { callStack       = scopeCallStack
                                      , generatorCaller = Nothing
                                      , contextMatch    = true
                                      }
            }
        $ evalThePack [] Map.empty args
        $ Map.toList kwargs


-- | utility makeOp(lhExpr, opSym, rhExpr)
makeOpProc :: EdhProcedure
makeOpProc !argsSender !exit =
  packEdhArgs argsSender $ \(ArgsPack args kwargs) -> if (not $ null kwargs)
    then throwEdh EvalError "No kwargs accepted by makeOp"
    else case args of
      [(EdhExpr _ !lhe _), EdhString op, (EdhExpr _ !rhe _)] ->
        exitEdhProc exit (edhExpr $ InfixExpr op lhe rhe)
      _ -> throwEdh EvalError $ "Invalid arguments to makeOp: " <> T.pack
        (show args)


-- | utility makeExpr(*args,**kwargs)
makeExprProc :: EdhProcedure
makeExprProc !argsSender !exit = case argsSender of
  []                    -> exitEdhProc exit nil
  [SendPosArg !argExpr] -> exitEdhProc exit (edhExpr argExpr)
  argSenders ->
    packEdhExprs argSenders $ \apk -> exitEdhProc exit $ EdhArgsPack apk

