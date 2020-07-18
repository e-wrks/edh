
module Language.Edh.Batteries.Reflect where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad.Reader
import           Control.Concurrent.STM

import           Data.Unique
import           Data.List.NonEmpty             ( (<|) )
import qualified Data.List.NonEmpty            as NE
import qualified Data.Text                     as T

import           Text.Megaparsec

import           Data.Lossless.Decimal          ( decimalToInteger )

import           Language.Edh.Control
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | utility constructor(*args,**kwargs)
ctorProc :: EdhProcedure
ctorProc (ArgsPack !args !kwargs) !exit = do
  !pgs <- ask
  let callerCtx   = edh'context pgs
      callerScope = contextScope callerCtx
      !argsCls    = edhClassOf <$> args
  if odNull kwargs
    then case argsCls of
      []  -> exitEdhProc exit (EdhClass $ objClass $ thisObject callerScope)
      [t] -> exitEdhProc exit t
      _   -> exitEdhProc exit $ EdhArgsPack $ ArgsPack argsCls odEmpty
    else exitEdhProc
      exit
      (EdhArgsPack $ ArgsPack argsCls $ odMap edhClassOf kwargs)
 where
  edhClassOf :: EdhValue -> EdhValue
  edhClassOf (EdhObject o) = EdhClass $ objClass o
  edhClassOf _             = nil

-- | utility supers(*args,**kwargs)
supersProc :: EdhProcedure
supersProc (ArgsPack !args !kwargs) !exit = do
  !pgs <- ask
  let !callerCtx   = edh'context pgs
      !callerScope = contextScope callerCtx
  if null args && odNull kwargs
    then contEdhSTM $ do
      supers <-
        map EdhObject <$> (readTVar $ objSupers $ thatObject callerScope)
      exitEdhSTM pgs exit $ EdhArgsPack $ ArgsPack supers odEmpty
    else if odNull kwargs
      then case args of
        [v] -> contEdhSTM $ do
          supers <- supersOf v
          exitEdhSTM pgs exit supers
        _ -> contEdhSTM $ do
          argsSupers <- sequence $ supersOf <$> args
          exitEdhSTM pgs exit $ EdhArgsPack $ ArgsPack argsSupers odEmpty
      else contEdhSTM $ do
        argsSupers   <- sequence $ supersOf <$> args
        kwargsSupers <- odMapSTM supersOf kwargs
        exitEdhSTM pgs exit (EdhArgsPack $ ArgsPack argsSupers kwargsSupers)
 where
  supersOf :: EdhValue -> STM EdhValue
  supersOf v = case v of
    EdhObject o -> map EdhObject <$> readTVar (objSupers o) >>= \supers ->
      return $ EdhArgsPack $ ArgsPack supers odEmpty
    _ -> return nil


-- | utility scope()
-- obtain current scope as reflected object
scopeObtainProc :: EdhProcedure
scopeObtainProc (ArgsPack _args !kwargs) !exit = do
  !pgs <- ask
  let !ctx = edh'context pgs
  case odLookup (AttrByName "ofObj") kwargs of
    Just (EdhObject ofObj) -> contEdhSTM $ do
      wrapperObj <- mkScopeWrapper ctx $ objectScope ctx ofObj
      exitEdhSTM pgs exit $ EdhObject wrapperObj
    _ -> do
      let unwind :: Int
          !unwind = case odLookup (AttrByName "unwind") kwargs of
            Just (EdhDecimal d) -> case decimalToInteger d of
              Just n  -> fromIntegral n
              Nothing -> 0
            _ -> 0
          scopeFromStack :: Int -> [Scope] -> (Scope -> STM ()) -> STM ()
          scopeFromStack _ [] _ = throwEdhSTM pgs UsageError "stack underflow"
          scopeFromStack c (f : _) !exit' | c <= 0 = exit' f
          scopeFromStack c (_ : s) !exit' = scopeFromStack (c - 1) s exit'
      contEdhSTM
        $ scopeFromStack unwind (NE.tail (callStack ctx))
        $ \tgtScope -> do
            wrapperObj <- mkScopeWrapper ctx tgtScope
            exitEdhSTM pgs exit $ EdhObject wrapperObj


-- | utility scope.attrs()
-- get attribute types in the scope
scopeAttrsProc :: EdhProcedure
scopeAttrsProc _ !exit = do
  !pgs <- ask
  let !that = thatObject $ contextScope $ edh'context pgs
  contEdhSTM $ do
    ps <- allEntityAttrs pgs $ scopeEntity $ wrappedScopeOf that
    exitEdhSTM pgs exit $ EdhArgsPack $ ArgsPack [] $ odFromList ps


-- | repr of a scope
scopeReprProc :: EdhProcedure
scopeReprProc _ !exit = do
  !pgs <- ask
  let !that                = thatObject $ contextScope $ edh'context pgs
      ProcDecl _ _ !spBody = procedure'decl $ objClass that
  exitEdhProc exit $ EdhString $ case spBody of
    Left (StmtSrc (srcLoc, _)) ->
      "#scope# " <> (T.pack $ sourcePosPretty srcLoc)
    Right _ -> "#host scope#"


-- | utility scope.lexiLoc()
-- get lexical source locations formated as a string, from the wrapped scope
scopeCallerLocProc :: EdhProcedure
scopeCallerLocProc _ !exit = do
  !pgs <- ask
  let !that = thatObject $ contextScope $ edh'context pgs
  case procedure'lexi $ objClass that of
    Nothing -> -- inner and outer of this scope are the two poles
      -- generated from *Taiji*, i.e. from oneness to duality
      exitEdhProc exit $ EdhString "<SupremeUltimate>"
    Just !callerLexi -> do
      let StmtSrc (!srcLoc, _) = scopeCaller callerLexi
      exitEdhProc exit $ EdhString $ T.pack $ sourcePosPretty srcLoc


-- | utility scope.lexiLoc()
-- get lexical source locations formated as a string, from the wrapped scope
scopeLexiLocProc :: EdhProcedure
scopeLexiLocProc _ !exit = do
  !pgs <- ask
  let !that                = thatObject $ contextScope $ edh'context pgs
      ProcDecl _ _ !spBody = procedure'decl $ objClass that
  exitEdhProc exit $ EdhString $ case spBody of
    Left  (StmtSrc (srcLoc, _)) -> T.pack $ sourcePosPretty srcLoc
    Right _                     -> "<host-code>"


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
      wrapperObj <- mkScopeWrapper ctx outer
      exitEdhSTM pgs exit $ EdhObject wrapperObj


-- | utility scope.get(k1, k2, n1=k3, n2=k4, ...)
-- get attribute values from the wrapped scope
scopeGetProc :: EdhProcedure
scopeGetProc (ArgsPack !args !kwargs) !exit = do
  !pgs <- ask
  let !callerCtx = edh'context pgs
      !that      = thatObject $ contextScope callerCtx
      !ent       = scopeEntity $ wrappedScopeOf that
      lookupAttrs
        :: [EdhValue]
        -> [(AttrKey, EdhValue)]
        -> [EdhValue]
        -> [(AttrKey, EdhValue)]
        -> (([EdhValue], [(AttrKey, EdhValue)]) -> STM ())
        -> STM ()
      lookupAttrs rtnArgs rtnKwArgs [] [] !exit' = exit' (rtnArgs, rtnKwArgs)
      lookupAttrs rtnArgs rtnKwArgs [] ((n, v) : restKwArgs) !exit' =
        attrKeyFrom pgs v $ \k -> do
          attrVal <- lookupEntityAttr pgs ent k
          lookupAttrs rtnArgs ((n, attrVal) : rtnKwArgs) [] restKwArgs exit'
      lookupAttrs rtnArgs rtnKwArgs (v : restArgs) kwargs' !exit' =
        attrKeyFrom pgs v $ \k -> do
          attrVal <- lookupEntityAttr pgs ent k
          lookupAttrs (attrVal : rtnArgs) rtnKwArgs restArgs kwargs' exit'
  contEdhSTM $ lookupAttrs [] [] args (odToList kwargs) $ \case
    ([v]    , []       ) -> exitEdhSTM pgs exit v
    (rtnArgs, rtnKwArgs) -> exitEdhSTM pgs exit $ EdhArgsPack $ ArgsPack
      (reverse rtnArgs)
      (odFromList rtnKwArgs)
 where
  attrKeyFrom :: EdhProgState -> EdhValue -> (AttrKey -> STM ()) -> STM ()
  attrKeyFrom _ (EdhString attrName) !exit' = exit' $ AttrByName attrName
  attrKeyFrom _ (EdhSymbol sym     ) !exit' = exit' $ AttrBySym sym
  attrKeyFrom pgs badVal _ =
    throwEdhSTM pgs UsageError $ "Invalid attribute reference type - " <> T.pack
      (edhTypeNameOf badVal)


-- | utility scope.put(k1:v1, k2:v2, n3=v3, n4=v4, ...)
-- put attribute values into the wrapped scope
scopePutProc :: EdhProcedure
scopePutProc (ArgsPack !args !kwargs) !exit = do
  !pgs <- ask
  let !callerCtx = edh'context pgs
      !that      = thatObject $ contextScope callerCtx
      !ent       = scopeEntity $ wrappedScopeOf that
  contEdhSTM $ putAttrs pgs args [] $ \attrs -> do
    updateEntityAttrs pgs ent $ attrs ++ odToList kwargs
    exitEdhSTM pgs exit nil
 where
  putAttrs
    :: EdhProgState
    -> [EdhValue]
    -> [(AttrKey, EdhValue)]
    -> ([(AttrKey, EdhValue)] -> STM ())
    -> STM ()
  putAttrs _   []           cumu !exit' = exit' cumu
  putAttrs pgs (arg : rest) cumu !exit' = case arg of
    EdhPair (EdhString !k) !v ->
      putAttrs pgs rest ((AttrByName k, v) : cumu) exit'
    EdhPair (EdhSymbol !k) !v ->
      putAttrs pgs rest ((AttrBySym k, v) : cumu) exit'
    _ ->
      throwEdhSTM pgs UsageError
        $  "Invalid key/value type to put into a scope - "
        <> T.pack (edhTypeNameOf arg)


-- | utility scope.eval(expr1, expr2, kw3=expr3, kw4=expr4, ...)
-- evaluate expressions in this scope
scopeEvalProc :: EdhProcedure
scopeEvalProc (ArgsPack !args !kwargs) !exit = do
  !pgs <- ask
  let !callerCtx      = edh'context pgs
      !that           = thatObject $ contextScope callerCtx
      !theScope       = wrappedScopeOf that
      -- eval all exprs with the original scope on top of current call stack
      !scopeCallStack = theScope <| callStack callerCtx
  if odNull kwargs && null args
    then exitEdhProc exit nil
    else contEdhSTM $ do
      let !pgsEval = pgs
            { edh'context = callerCtx { callStack        = scopeCallStack
                                      , generatorCaller  = Nothing
                                      , contextMatch     = true
                                      , contextPure      = False
                                      , contextExporting = False
                                      }
            }
      kwIOPD <- iopdEmpty
      let
        evalThePack
          :: [EdhValue] -> [EdhValue] -> [(AttrKey, EdhValue)] -> STM ()
        evalThePack !argsValues [] [] =
          iopdToList kwIOPD >>= \ !kwargsValues ->
            -- restore original program state and return the eval-ed values
            exitEdhSTM pgs exit $ case argsValues of
              [val] | null kwargsValues -> val
              _ -> EdhArgsPack $ ArgsPack (reverse argsValues) $ odFromList
                kwargsValues
        evalThePack !argsValues [] (kwExpr : kwargsExprs') = case kwExpr of
          (!kw, EdhExpr _ !expr _) ->
            runEdhProc pgsEval $ evalExpr expr $ \(OriginalValue !val _ _) ->
              contEdhSTM $ do
                iopdInsert kw (edhDeCaseClose val) kwIOPD
                evalThePack argsValues [] kwargsExprs'
          v -> throwEdhSTM pgs EvalError $ "Not an expr: " <> T.pack (show v)
        evalThePack !argsValues (!argExpr : argsExprs') !kwargsExprs =
          case argExpr of
            EdhExpr _ !expr _ ->
              runEdhProc pgsEval $ evalExpr expr $ \(OriginalValue !val _ _) ->
                contEdhSTM $ evalThePack (edhDeCaseClose val : argsValues)
                                         argsExprs'
                                         kwargsExprs
            v -> throwEdhSTM pgs EvalError $ "Not an expr: " <> T.pack (show v)
      evalThePack [] args $ odToList kwargs


-- | utility makeOp(lhExpr, opSym, rhExpr)
makeOpProc :: EdhProcedure
makeOpProc (ArgsPack !args !kwargs) !exit = do
  pgs <- ask
  if (not $ odNull kwargs)
    then throwEdh EvalError "No kwargs accepted by makeOp"
    else case args of
      [(EdhExpr _ !lhe _), EdhString op, (EdhExpr _ !rhe _)] -> contEdhSTM $ do
        xu <- unsafeIOToSTM newUnique
        exitEdhSTM pgs exit $ EdhExpr xu (InfixExpr op lhe rhe) ""
      _ -> throwEdh EvalError $ "Invalid arguments to makeOp: " <> T.pack
        (show args)

