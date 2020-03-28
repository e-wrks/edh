
module Language.Edh.Batteries.Ctrl where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Maybe
import           Data.Unique
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.Evaluate


-- | operator ($=>) - the `catch`
--
-- the right-hand-expr will only be eval'ed  when an exception occurred
-- in its left-hand-expr;
-- the exception value is the context match target during eval of the
-- right-hand-expr;
-- the exceptin is assused to have been recovered, if the rhe evals as
-- matched (i.e. not to a value of <fallthrough>), or the exception will
-- keep propagating, i.e. re-thrown.
catchProc :: EdhIntrinsicOp
catchProc !tryExpr !catchExpr !exit =
  edhCatch (evalExpr tryExpr) exit $ \recover rethrow -> ask >>= \pgs ->
    case contextMatch $ edh'context pgs of
      EdhNil -> rethrow -- no error occurred, no catch
      _ -> -- try recover by catch expression
        evalMatchingExpr catchExpr
          $ \recoverResult@(OriginalValue recoverVal _ _) -> case recoverVal of
              EdhFallthrough -> rethrow -- not to recover
              _              -> exitEdhProc' recover recoverResult

-- | operator (@=>) - the `finally`
--
-- the right-hand-expr will always be eval'ed whether the left-hand-expr
-- has caused exeption or not;
-- the exception value (or nil if none occurred) is the context match
-- target during eval of the right-hand-expr;
-- an exception if occurred, will never be assumed as recovered by the
-- right-hand-expr.
finallyProc :: EdhIntrinsicOp
finallyProc !tryExpr !finallyExpr !exit = edhCatch (evalExpr tryExpr) exit
  $ \_ rethrow -> evalMatchingExpr finallyExpr $ const rethrow


-- | operator (->) - the brancher, if its left-hand matches, early stop its
-- enclosing code block (commonly a case-of block, but other blocks as well),
-- with eval-ed result of its right-hand, unless the right-hand result is
-- `fallthrough`
branchProc :: EdhIntrinsicOp
branchProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  let !callerCtx   = edh'context pgs
      !callerScope = contextScope callerCtx
      !ctxMatch    = contextMatch callerCtx
      updAttrs :: [(AttrKey, EdhValue)] -> STM ()
      updAttrs [] = -- todo: which one is semantically more correct ?
        -- to trigger a write, or avoid the write
        return ()  -- this avoids triggering stm write
      updAttrs !ps' = updateEntityAttrs pgs (scopeEntity callerScope) ps'
      branchMatched :: [(AttrName, EdhValue)] -> STM ()
      branchMatched !ps = do
        updAttrs [ (AttrByName n, noneNil v) | (n, v) <- ps, n /= "_" ]
        runEdhProc pgs $ evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
          exitEdhProc
            exit
            (case rhVal of
              EdhFallthrough -> rhVal
              EdhCaseClose{} -> rhVal
              _              -> EdhCaseClose rhVal
            )

      handlePairPattern !pairPattern =
        case matchPairPattern pairPattern ctxMatch [] of
          Nothing -> throwEdh EvalError $ "Invalid pair pattern: " <> T.pack
            (show pairPattern)
          Just [] -> -- valid pattern, no match
            exitEdhProc exit EdhFallthrough
          Just !mps -> contEdhSTM $ branchMatched mps

  case lhExpr of
    -- recognize `_` as similar to the wildcard pattern match in Haskell,
    -- it always matches
    AttrExpr (DirectRef (NamedAttr "_")) -> contEdhSTM $ branchMatched []

    -- TODO support nested patterns

    -- { x:y:z:... } -- pair pattern matching
    DictExpr [pairPattern              ] -> handlePairPattern pairPattern
    -- this is to establish the intuition that `{ ... }` always invokes
    -- pattern matching. if a literal dict value really meant to be matched,
    -- the parenthesized form `( {k1: v1, k2: v2, ...} )` should be used.
    DictExpr !malPairs ->
      throwEdh EvalError $ "Invalid match pattern: " <> T.pack (show malPairs)

    -- other patterns matching
    BlockExpr patternExpr -> case patternExpr of

      -- {( x:y:z:... )} -- parenthesised pair pattern
      [StmtSrc (_, ExprStmt (ParenExpr pairPattern))] ->
        handlePairPattern pairPattern

      -- { continue } -- match with continue
      [StmtSrc (_, ContinueStmt)] -> case ctxMatch of
        EdhContinue -> contEdhSTM $ branchMatched []
        _           -> exitEdhProc exit EdhFallthrough

      -- { val } -- wild capture pattern, used to capture a non-nil result as
      -- an attribute.
      -- Note: a raw nil value should be value-matched explicitly
      [StmtSrc (_, ExprStmt (AttrExpr (DirectRef (NamedAttr attrName))))] ->
        case ctxMatch of -- don't match raw nil here, 
          EdhNil -> exitEdhProc exit EdhFallthrough
          -- but a named nil (i.e. None/Nothing etc.) should be matched
          _      -> contEdhSTM $ branchMatched [(attrName, ctxMatch)]

      -- { term := value } -- definition pattern
      [StmtSrc (_, ExprStmt (InfixExpr ":=" (AttrExpr (DirectRef (NamedAttr termName))) (AttrExpr (DirectRef (NamedAttr valueName)))))]
        -> contEdhSTM $ case ctxMatch of
          EdhNamedValue !n !v ->
            branchMatched [(termName, EdhString n), (valueName, v)]
          _ -> exitEdhSTM pgs exit EdhFallthrough

      -- { head => tail } -- snoc pattern
      [StmtSrc (_, ExprStmt (InfixExpr "=>" (AttrExpr (DirectRef (NamedAttr headName))) (AttrExpr (DirectRef (NamedAttr tailName)))))]
        -> let doMatched headVal tailVal =
                   branchMatched [(headName, headVal), (tailName, tailVal)]
           in  contEdhSTM $ case ctxMatch of
                 EdhArgsPack (ArgsPack (h : rest) !kwargs) | Map.null kwargs ->
                   doMatched h (EdhArgsPack (ArgsPack rest kwargs))
                 EdhTuple (h    : rest) -> doMatched h (EdhTuple rest)
                 EdhList  (List _ !l  ) -> readTVar l >>= \case
                   (h : rest) -> do
                     rl <- newTVar rest
                     u  <- unsafeIOToSTM newUnique
                     doMatched h $ EdhList $ List u rl
                   _ -> exitEdhSTM pgs exit EdhFallthrough
                 _ -> exitEdhSTM pgs exit EdhFallthrough

      -- {( x,y,z,... )} -- tuple pattern
      [StmtSrc (_, ExprStmt (TupleExpr vExprs))] -> contEdhSTM $ if null vExprs
        then -- an empty tuple pattern matches any empty sequence
             case ctxMatch of
          EdhArgsPack (ArgsPack [] !kwargs) | Map.null kwargs ->
            branchMatched []
          EdhTuple [] -> branchMatched []
          EdhList (List _ !l) ->
            readTVar l
              >>= \ll -> if null ll
                    then branchMatched []
                    else exitEdhSTM pgs exit EdhFallthrough
          _ -> exitEdhSTM pgs exit EdhFallthrough
        else do
          attrNames <- fmap catMaybes $ sequence $ (<$> vExprs) $ \case
            (AttrExpr (DirectRef (NamedAttr vAttr))) -> return $ Just vAttr
            _ -> return Nothing
          if length attrNames /= length vExprs
            then throwEdhSTM
              pgs
              UsageError
              ("Invalid element in tuple pattern: " <> T.pack (show vExprs))
            else case ctxMatch of
              EdhTuple vs | length vs == length vExprs ->
                branchMatched $ zip attrNames vs
              _ -> exitEdhSTM pgs exit EdhFallthrough

      -- {{ class:inst }} -- instance resolving pattern
      [StmtSrc (_, ExprStmt (DictExpr [InfixExpr ":" (AttrExpr (DirectRef (NamedAttr classAttr))) (AttrExpr (DirectRef (NamedAttr instAttr)))]))]
        -> -- brittany insists on putting together the long line above, any workaround?
           case ctxMatch of
          EdhObject ctxObj ->
            contEdhSTM
              $   lookupEdhCtxAttr pgs callerScope (AttrByName classAttr)
              >>= \case
                    EdhNil -> exitEdhSTM pgs exit EdhFallthrough
                    val    -> case val of
                      EdhClass class_ ->
                        resolveEdhInstance pgs class_ ctxObj >>= \case
                          Just instObj ->
                            branchMatched [(instAttr, EdhObject instObj)]
                          Nothing -> exitEdhSTM pgs exit EdhFallthrough
                      _ ->
                        throwEdhSTM pgs EvalError
                          $  "Invalid class "
                          <> classAttr
                          <> ", it is a "
                          <> T.pack (edhTypeNameOf val)
                          <> ": "
                          <> T.pack (show val)
          _ -> exitEdhProc exit EdhFallthrough

      -- {[ x,y,z,... ]} -- any-of pattern
      [StmtSrc (_, ExprStmt (ListExpr vExprs))] -> if null vExprs
        then exitEdhProc exit EdhFallthrough
        else evalExprs vExprs $ \(OriginalValue matchVals _ _) ->
          case matchVals of
            EdhTuple l -> if ctxMatch `elem` l
              then contEdhSTM $ branchMatched []
              else exitEdhProc exit EdhFallthrough
            _ -> error "bug: evalExprs returned non-tuple"


      -- TODO more kinds of match patterns to support ?
      --      e.g. list pattern, with rest-items repacking etc.
      _ -> throwEdh EvalError $ "Invalid match pattern: " <> T.pack
        (show patternExpr)

    -- guarded condition, ignore match target in context, just check if the
    -- condition itself is true
    PrefixExpr Guard guardedExpr ->
      evalExpr guardedExpr $ \(OriginalValue !predValue _ _) ->
        if predValue /= true
          then exitEdhProc exit EdhFallthrough
          else contEdhSTM $ branchMatched []

    -- value-wise matching against the target in context
    _ -> evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
      let namelyMatch :: EdhValue -> EdhValue -> Bool
          namelyMatch (EdhNamedValue x'n x'v) (EdhNamedValue y'n y'v) =
              x'n == y'n && x'v == y'v
          namelyMatch EdhNamedValue{} _               = False
          namelyMatch _               EdhNamedValue{} = False
          namelyMatch x               y               = x == y
      in  if not $ namelyMatch lhVal ctxMatch
            then exitEdhProc exit EdhFallthrough
            else contEdhSTM $ branchMatched []


-- | `Nothing` means invalid pattern, `[]` means no match, non-empty list is
-- the aligned values along with attr names as matched
matchPairPattern
  :: Expr -> EdhValue -> [(AttrName, EdhValue)] -> Maybe [(AttrName, EdhValue)]
matchPairPattern p v matches = case p of
  InfixExpr ":" leftExpr (AttrExpr (DirectRef (NamedAttr vAttr))) -> case v of
    EdhPair leftVal val ->
      let matches' = (vAttr, val) : matches
      in  case leftExpr of
            (AttrExpr (DirectRef (NamedAttr leftAttr))) -> case leftVal of
              EdhPair _ _ -> Just []
              _           -> Just $ (leftAttr, leftVal) : matches'
            InfixExpr ":" _ _ -> matchPairPattern leftExpr leftVal matches'
            _                 -> Nothing
    _ -> Just []
  _ -> Nothing
