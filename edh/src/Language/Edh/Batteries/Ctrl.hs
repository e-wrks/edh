
module Language.Edh.Batteries.Ctrl where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad.Reader

import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Maybe
import           Data.Unique
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.Evaluate


-- | operator (::) - arbitrary annotation
--
-- this should have lowest possible precedence and do nothing when eval'ed
-- so an arbitrary expression, so long as it's syntactically correct,
-- can be placed anywhere serving annotation purpose e.g.
--
--   abs :: ( DecimalType ) -> DecimalType
--   method abs( n ) n<0 &> ( -n ) |> n
--
--   x :: StringType
--   x = 'Hello'
--
annoProc :: EdhIntrinsicOp
annoProc _ _ !exit = exitEdhProc exit nil


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
        evalExpr catchExpr $ \recoverResult@(OriginalValue recoverVal _ _) ->
          case recoverVal of
            EdhRethrow -> rethrow -- not to recover
            EdhCaseClose val ->
              -- don't bubble up the close-of-case, as `catch` is not a branch 
              exitEdhProc' recover recoverResult { valueFromOrigin = val }
            EdhCaseOther   -> rethrow -- not to recover
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
finallyProc !tryExpr !finallyExpr !exit = ask >>= \pgs -> contEdhSTM $ do
  hndlrTh <- unsafeIOToSTM myThreadId
  edhCatchSTM pgs
              (\ !pgsTry !exit' -> runEdhProc pgsTry $ evalExpr tryExpr exit')
              exit
    $ \pgsThrower !exv _recover !rethrow -> do
        fnlyTh <- unsafeIOToSTM myThreadId
        if fnlyTh /= hndlrTh
          then -- don't run the finally block from a different thread other
               -- than the handler installer
               rethrow
          else
            runEdhProc pgsThrower
              { edh'context = (edh'context pgs) { contextMatch = exv }
              }
            $ evalExpr finallyExpr
            $ const
            $ contEdhSTM rethrow


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
          exitEdhProc exit $ case rhVal of
            -- a nested branch matched, the outer branch eval to its final
            -- value with case closed
            EdhCaseClose !nestedMatch ->
              EdhCaseClose $ edhDeCaseClose nestedMatch
            -- a nested branch mismatched, while the outer branch did match,
            -- so eval to nil with case closed
            EdhCaseOther   -> EdhCaseClose nil
            -- propagate an explicit fallthrough
            EdhFallthrough -> EdhFallthrough
            -- some other value, the outer branch eval to it
            _              -> EdhCaseClose rhVal

      handlePairPattern !maybeName1 !pairPattern =
        case matchPairPattern pairPattern ctxMatch [] of
          Nothing -> throwEdh EvalError $ "Invalid pair pattern: " <> T.pack
            (show pairPattern)
          Just (_, []) -> -- valid pattern, no match
            exitEdhProc exit EdhCaseOther
          Just (resi, mps) -> case maybeName1 of
            Just !name1 -> case resi of
              Nothing    -> exitEdhProc exit EdhCaseOther
              Just !val1 -> contEdhSTM $ branchMatched $ (name1, val1) : mps
            Nothing -> case resi of
              Nothing -> contEdhSTM $ branchMatched mps
              Just{}  -> exitEdhProc exit EdhCaseOther

  case lhExpr of
    -- recognize `_` as similar to the wildcard pattern match in Haskell,
    -- it always matches
    AttrExpr (DirectRef (NamedAttr "_")) -> contEdhSTM $ branchMatched []

    -- TODO support nested patterns

    -- { x:y:z:... } -- pair pattern matching
    DictExpr [(AddrDictKey (DirectRef (NamedAttr !name1)), pairPattern)] ->
      handlePairPattern (Just name1) pairPattern
    -- this is to establish the intuition that `{ ... }` always invokes
    -- pattern matching. if a literal dict value really meant to be matched,
    -- the parenthesized form `( {k1: v1, k2: v2, ...} )` should be used.
    DictExpr !malPairs ->
      throwEdh EvalError $ "Invalid match pattern: " <> T.pack (show malPairs)

    -- other patterns matching
    BlockExpr patternExpr -> case patternExpr of

      -- {( x )} -- single arg 
      [StmtSrc (_, ExprStmt (ParenExpr (AttrExpr (DirectRef (NamedAttr attrName)))))]
        -> case ctxMatch of
          EdhArgsPack (ArgsPack [argVal] !kwargs) | Map.null kwargs ->
            contEdhSTM $ branchMatched [(attrName, argVal)]
          _ -> exitEdhProc exit EdhCaseOther

      -- {( x:y:z:... )} -- parenthesised pair pattern
      [StmtSrc (_, ExprStmt (ParenExpr pairPattern@(InfixExpr ":" _ _)))] ->
        handlePairPattern Nothing pairPattern

      -- { continue } -- match with continue
      [StmtSrc (_, ContinueStmt)] -> case ctxMatch of
        EdhContinue -> contEdhSTM $ branchMatched []
        _           -> exitEdhProc exit EdhCaseOther

      -- { break } -- match with break
      [StmtSrc (_, BreakStmt)] -> case ctxMatch of
        EdhBreak -> contEdhSTM $ branchMatched []
        _        -> exitEdhProc exit EdhCaseOther

      -- { fallthrough } -- match with fallthrough
      [StmtSrc (_, FallthroughStmt)] -> case ctxMatch of
        EdhFallthrough -> contEdhSTM $ branchMatched []
        _              -> exitEdhProc exit EdhCaseOther

      -- { return nil } -- match with nil return
      [StmtSrc (_, ReturnStmt (LitExpr NilLiteral))] -> case ctxMatch of
        EdhReturn EdhNil -> contEdhSTM $ branchMatched []
        _                -> exitEdhProc exit EdhCaseOther

      -- { return xx } -- match with value return
      [StmtSrc (_, ReturnStmt (AttrExpr (DirectRef (NamedAttr attrName))))] ->
        case ctxMatch of
          EdhReturn !rtnVal | rtnVal /= EdhNil ->
            contEdhSTM $ branchMatched [(attrName, rtnVal)]
          _ -> exitEdhProc exit EdhCaseOther

      -- { val } -- wild capture pattern, used to capture a non-nil result as
      -- an attribute.
      -- Note: a raw nil value should be value-matched explicitly
      [StmtSrc (_, ExprStmt (AttrExpr (DirectRef (NamedAttr attrName))))] ->
        case ctxMatch of -- don't match raw nil here, 
          EdhNil -> exitEdhProc exit EdhCaseOther
          -- but a named nil (i.e. None/Nothing etc.) should be matched
          _      -> contEdhSTM $ branchMatched [(attrName, ctxMatch)]

      -- { term := value } -- definition pattern
      [StmtSrc (_, ExprStmt (InfixExpr ":=" (AttrExpr (DirectRef (NamedAttr termName))) (AttrExpr (DirectRef (NamedAttr valueName)))))]
        -> contEdhSTM $ case ctxMatch of
          EdhNamedValue !n !v ->
            branchMatched [(termName, EdhString n), (valueName, v)]
          _ -> exitEdhSTM pgs exit EdhCaseOther

      -- { head => tail } -- uncons pattern
      [StmtSrc (_, ExprStmt (InfixExpr "=>" (AttrExpr (DirectRef (NamedAttr headName))) (AttrExpr (DirectRef (NamedAttr tailName)))))]
        -> let doMatched headVal tailVal =
                   branchMatched [(headName, headVal), (tailName, tailVal)]
           in  contEdhSTM $ case ctxMatch of
                 EdhArgsPack (ArgsPack (h : rest) !kwargs) | Map.null kwargs ->
                   doMatched h (EdhArgsPack (ArgsPack rest kwargs))
                 EdhList (List _ !l) -> readTVar l >>= \case
                   (h : rest) -> do
                     rl <- newTVar rest
                     u  <- unsafeIOToSTM newUnique
                     doMatched h $ EdhList $ List u rl
                   _ -> exitEdhSTM pgs exit EdhCaseOther
                 _ -> exitEdhSTM pgs exit EdhCaseOther

      -- { prefix @< match >@ suffix } -- sub-string cut pattern
      [StmtSrc (_, ExprStmt (InfixExpr ">@" (InfixExpr "@<" (AttrExpr (DirectRef (NamedAttr prefixName))) matchExpr) (AttrExpr (DirectRef (NamedAttr suffixName)))))]
        -> case ctxMatch of
          EdhString !fullStr ->
            evalExpr matchExpr $ \(OriginalValue !mVal _ _) ->
              edhValueStr (edhUltimate mVal) $ \(OriginalValue !mStrVal _ _) ->
                case mStrVal of
                  EdhString !mStr -> if T.null mStr
                    then throwEdh UsageError
                                  "You don't use empty string for match"
                    else
                      let (prefix, rest) = T.breakOn mStr fullStr
                      in
                        case T.stripPrefix mStr rest of
                          Just !suffix ->
                            contEdhSTM
                              $ branchMatched
                                  [ (prefixName, EdhString prefix)
                                  , (suffixName, EdhString suffix)
                                  ]
                          _ -> exitEdhProc exit EdhCaseOther
                  _ -> error "bug: edhValueStr returned non-string"
          _ -> exitEdhProc exit EdhCaseOther

      -- { match >@ suffix } -- prefix cut pattern
      [StmtSrc (_, ExprStmt (InfixExpr ">@" prefixExpr (AttrExpr (DirectRef (NamedAttr suffixName)))))]
        -> case ctxMatch of
          EdhString !fullStr ->
            evalExpr prefixExpr $ \(OriginalValue !lhVal _ _) ->
              edhValueStr (edhUltimate lhVal)
                $ \(OriginalValue !lhStrVal _ _) -> case lhStrVal of
                    EdhString !lhStr -> case T.stripPrefix lhStr fullStr of
                      Just !suffix -> contEdhSTM
                        $ branchMatched [(suffixName, EdhString suffix)]
                      _ -> exitEdhProc exit EdhCaseOther
                    _ -> error "bug: edhValueStr returned non-string"
          _ -> exitEdhProc exit EdhCaseOther

      -- { prefix @< match } -- suffix cut pattern
      [StmtSrc (_, ExprStmt (InfixExpr "@<" (AttrExpr (DirectRef (NamedAttr prefixName))) suffixExpr))]
        -> case ctxMatch of
          EdhString !fullStr ->
            evalExpr suffixExpr $ \(OriginalValue !rhVal _ _) ->
              edhValueStr (edhUltimate rhVal)
                $ \(OriginalValue !rhStrVal _ _) -> case rhStrVal of
                    EdhString !rhStr -> case T.stripSuffix rhStr fullStr of
                      Just !prefix -> contEdhSTM
                        $ branchMatched [(prefixName, EdhString prefix)]
                      _ -> exitEdhProc exit EdhCaseOther
                    _ -> error "bug: edhValueStr returned non-string"
          _ -> exitEdhProc exit EdhCaseOther

      -- {( x,y,z,... )} -- pattern matching number of positional args
      [StmtSrc (_, ExprStmt (ArgsPackExpr !argSenders))] ->
        contEdhSTM $ if null argSenders
          then case ctxMatch of
            -- an empty apk pattern matches any empty sequence
            EdhArgsPack (ArgsPack [] !kwargs) | Map.null kwargs ->
              branchMatched []
            EdhList (List _ !l) ->
              readTVar l
                >>= \ll -> if null ll
                      then branchMatched []
                      else exitEdhSTM pgs exit EdhCaseOther
            _ -> exitEdhSTM pgs exit EdhCaseOther
          else do
            attrNames <- fmap catMaybes $ sequence $ (<$> argSenders) $ \case
              SendPosArg (AttrExpr (DirectRef (NamedAttr vAttr))) ->
                return $ Just vAttr
              _ -> return Nothing
            if length attrNames /= length argSenders
              then throwEdhSTM
                pgs
                UsageError
                ("Invalid element in apk pattern: " <> T.pack (show argSenders))
              else case ctxMatch of
                EdhArgsPack (ArgsPack !args !kwargs)
                  | length args == length argSenders && Map.null kwargs -> branchMatched
                  $ zip attrNames args
                _ -> exitEdhSTM pgs exit EdhCaseOther

      -- {{ class:inst }} -- instance resolving pattern
      [StmtSrc (_, ExprStmt (DictExpr [(AddrDictKey !clsAddr, AttrExpr (DirectRef (NamedAttr instAttr)))]))]
        -> -- brittany insists on putting together the long line above, any workaround?
           case ctxMatch of
          EdhObject ctxObj ->
            evalAttrAddr clsAddr $ \(OriginalValue !clsVal _ _) ->
              case clsVal of
                EdhNil -> exitEdhProc exit EdhCaseOther
                EdhClass !cls ->
                  contEdhSTM $ resolveEdhInstance pgs cls ctxObj >>= \case
                    Just instObj ->
                      branchMatched [(instAttr, EdhObject instObj)]
                    Nothing -> exitEdhSTM pgs exit EdhCaseOther
                _ ->
                  throwEdh EvalError
                    $  T.pack
                    $  "Invalid class "
                    <> show clsAddr
                    <> ", it is a "
                    <> edhTypeNameOf clsVal
                    <> ": "
                    <> show clsVal
          _ -> exitEdhProc exit EdhCaseOther

      -- {[ x,y,z,... ]} -- any-of pattern
      [StmtSrc (_, ExprStmt (ListExpr vExprs))] -> if null vExprs
        then exitEdhProc exit EdhCaseOther
        else evalExprs vExprs $ \(OriginalValue matchVals _ _) ->
          case matchVals of
            EdhArgsPack (ArgsPack !l _) -> if ctxMatch `elem` l
              then contEdhSTM $ branchMatched []
              else exitEdhProc exit EdhCaseOther
            _ -> error "bug: evalExprs returned non-apk"


      -- TODO more kinds of match patterns to support ?
      --      e.g. list pattern, with rest-items repacking etc.
      _ -> throwEdh EvalError $ "Invalid match pattern: " <> T.pack
        (show patternExpr)

    -- guarded condition, ignore match target in context, just check if the
    -- condition itself is true
    PrefixExpr Guard guardedExpr ->
      evalExpr guardedExpr $ \(OriginalValue !predValue _ _) ->
        if edhDeCaseClose predValue /= true
          then exitEdhProc exit EdhCaseOther
          else contEdhSTM $ branchMatched []

    -- value-wise matching against the target in context
    _ -> evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
      let namelyMatch :: EdhValue -> EdhValue -> Bool
          namelyMatch (EdhNamedValue x'n x'v) (EdhNamedValue y'n y'v) =
              x'n == y'n && x'v == y'v
          namelyMatch EdhNamedValue{} _               = False
          namelyMatch _               EdhNamedValue{} = False
          namelyMatch x               y               = x == y
      in  if not $ namelyMatch (edhDeCaseClose lhVal) ctxMatch
            then exitEdhProc exit EdhCaseOther
            else contEdhSTM $ branchMatched []


-- | `Nothing` means invalid pattern, `[]` means no match, non-empty list is
-- the aligned values along with attr names as matched
matchPairPattern
  :: Expr
  -> EdhValue
  -> [(AttrName, EdhValue)]
  -> Maybe (Maybe EdhValue, [(AttrName, EdhValue)])
matchPairPattern !p !v !matches = case p of
  AttrExpr (DirectRef (NamedAttr !lastAttr)) -> case v of
    EdhPair !resi !lastVal -> Just (Just resi, (lastAttr, lastVal) : matches)
    _                      -> Just (Nothing, (lastAttr, v) : matches)
  InfixExpr ":" !leftExpr (AttrExpr (DirectRef (NamedAttr !vAttr))) ->
    case v of
      EdhPair !leftVal !val ->
        let matches' = (vAttr, val) : matches
        in  case leftExpr of
              (AttrExpr (DirectRef (NamedAttr !leftAttr))) -> case leftVal of
                EdhPair !resi !lastVal ->
                  Just (Just resi, (leftAttr, lastVal) : matches')
                _ -> Just (Nothing, (leftAttr, leftVal) : matches')
              InfixExpr ":" _ _ -> matchPairPattern leftExpr leftVal matches'
              _                 -> Nothing
      _ -> Just (Nothing, [])
  _ -> Nothing
