
module Language.Edh.Batteries.Ctrl where

import           Prelude
-- import           Debug.Trace
-- import           System.IO.Unsafe

import           GHC.Conc

import           Data.Maybe
import           Data.Unique
import qualified Data.Text                     as T

import           Language.Edh.Control
import           Language.Edh.Details.IOPD
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
annoProc _ _ !exit = exitEdhTx exit nil


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
catchProc !tryExpr !catchExpr !exit !etsOuter =
  edhCatch etsOuter (evalExpr tryExpr) (exitEdh etsOuter exit)
    $ \ !etsThrower !exv recover rethrow -> case exv of
        EdhNil -> rethrow nil -- no exception has occurred, no catch
        _ -> -- eval the catch expression to see if it recovers or not
          let !ctxOuter = edh'context etsOuter
              !ctxHndl  = ctxOuter { edh'ctx'match = exv }
              !etsHndl  = etsThrower { edh'context = ctxHndl }
          in  runEdhTx etsHndl $ evalExpr catchExpr $ \ !catchResult _ets ->
                case edhDeCaseClose catchResult of

                  -- these results all mean no recovery, i.e. to rethrow
                  EdhRethrow     -> rethrow exv -- explicit rethrow
                  EdhFallthrough -> rethrow exv -- explicit fallthrough
                  EdhCaseOther   -> rethrow exv -- implicit none-match

                  -- other results are regarded as valid recovery
                  -- note `nil` included
                  !recoverVal    -> recover recoverVal

-- | operator (@=>) - the `finally`
--
-- the right-hand-expr will always be eval'ed whether the left-hand-expr
-- has caused exeption or not;
-- the exception value (or nil if none occurred) is the context match
-- target during eval of the right-hand-expr;
-- an exception if occurred, will never be assumed as recovered by the
-- right-hand-expr.
finallyProc :: EdhIntrinsicOp
finallyProc !tryExpr !finallyExpr !exit !etsOuter =
  edhCatch etsOuter (evalExpr tryExpr) (exitEdh etsOuter exit)
    $ \ !etsThrower !exv _recover !rethrow ->
        -- note this @passOn@ won't be triggered on a different (descendant)
        -- thread, in case no exception has occurred
        let !ctxOuter = edh'context etsOuter
            !ctxHndl  = ctxOuter { edh'ctx'match = exv }
            !etsHndl  = etsThrower { edh'context = ctxHndl }
        in  runEdhTx etsHndl $ evalExpr finallyExpr $ \_result _ets ->
              rethrow exv


-- | operator (->) - the brancher, if its left-hand matches, early stop its
-- enclosing code block (commonly a case-of block, but other blocks as well),
-- with eval-ed result of its right-hand, unless the right-hand result is
-- `fallthrough`
branchProc :: EdhIntrinsicOp
branchProc !lhExpr !rhExpr !exit !ets = case lhExpr of
    -- recognize `_` as similar to the wildcard pattern match in Haskell,
    -- it always matches
  AttrExpr (DirectRef (NamedAttr "_")) -> branchMatched []

  -- TODO support nested patterns

  -- { x:y:z:... } -- pair pattern matching
  DictExpr [(AddrDictKey (DirectRef (NamedAttr !name1)), pairPattern)] ->
    handlePairPattern (Just name1) pairPattern
  -- this is to establish the intuition that `{ ... }` always invokes
  -- pattern matching. if a literal dict value really meant to be matched,
  -- the parenthesized form `( {k1: v1, k2: v2, ...} )` should be used.
  DictExpr !malPairs ->
    throwEdh ets EvalError $ "invalid match pattern: " <> T.pack (show malPairs)

  -- other patterns matching
  BlockExpr patternExpr -> case patternExpr of

    -- {( x )} -- single arg 
    [StmtSrc (_, ExprStmt (ParenExpr (AttrExpr (DirectRef (NamedAttr attrName)))))]
      -> case ctxMatch of
        EdhArgsPack (ArgsPack [argVal] !kwargs) | odNull kwargs ->
          branchMatched [(attrName, argVal)]
        _ -> exitEdh ets exit EdhCaseOther

    -- {( x:y:z:... )} -- parenthesised pair pattern
    [StmtSrc (_, ExprStmt (ParenExpr pairPattern@(InfixExpr ":" _ _)))] ->
      handlePairPattern Nothing pairPattern

    -- { continue } -- match with continue
    [StmtSrc (_, ContinueStmt)] -> case ctxMatch of
      EdhContinue -> branchMatched []
      _           -> exitEdh ets exit EdhCaseOther

    -- { break } -- match with break
    [StmtSrc (_, BreakStmt)] -> case ctxMatch of
      EdhBreak -> branchMatched []
      _        -> exitEdh ets exit EdhCaseOther

    -- { fallthrough } -- match with fallthrough
    [StmtSrc (_, FallthroughStmt)] -> case ctxMatch of
      EdhFallthrough -> branchMatched []
      _              -> exitEdh ets exit EdhCaseOther

    -- { return nil } -- match with nil return
    [StmtSrc (_, ReturnStmt (LitExpr NilLiteral))] -> case ctxMatch of
      EdhReturn EdhNil -> branchMatched []
      _                -> exitEdh ets exit EdhCaseOther

    -- { return xx } -- match with value return
    [StmtSrc (_, ReturnStmt (AttrExpr (DirectRef (NamedAttr attrName))))] ->
      case ctxMatch of
        EdhReturn !rtnVal | rtnVal /= EdhNil ->
          branchMatched [(attrName, rtnVal)]
        _ -> exitEdh ets exit EdhCaseOther

    -- { val } -- wild capture pattern, used to capture a non-nil result as
    -- an attribute.
    -- Note: a raw nil value should be value-matched explicitly
    [StmtSrc (_, ExprStmt (AttrExpr (DirectRef (NamedAttr attrName))))] ->
      case ctxMatch of -- don't match raw nil here, 
        EdhNil -> exitEdh ets exit EdhCaseOther
        -- but a named nil (i.e. None/Nothing etc.) should be matched
        _      -> branchMatched [(attrName, ctxMatch)]

    -- { term := value } -- definition pattern
    [StmtSrc (_, ExprStmt (InfixExpr ":=" (AttrExpr (DirectRef (NamedAttr termName))) (AttrExpr (DirectRef (NamedAttr valueName)))))]
      -> case ctxMatch of
        EdhNamedValue !n !v ->
          branchMatched [(termName, EdhString n), (valueName, v)]
        _ -> exitEdh ets exit EdhCaseOther

    -- { head => tail } -- uncons pattern
    [StmtSrc (_, ExprStmt (InfixExpr "=>" (AttrExpr (DirectRef (NamedAttr headName))) (AttrExpr (DirectRef (NamedAttr tailName)))))]
      -> let doMatched headVal tailVal =
                 branchMatched [(headName, headVal), (tailName, tailVal)]
         in  case ctxMatch of
               EdhArgsPack (ArgsPack (h : rest) !kwargs) | odNull kwargs ->
                 doMatched h (EdhArgsPack (ArgsPack rest kwargs))
               EdhList (List _ !l) -> readTVar l >>= \case
                 (h : rest) -> do
                   rl <- newTVar rest
                   u  <- unsafeIOToSTM newUnique
                   doMatched h $ EdhList $ List u rl
                 _ -> exitEdh ets exit EdhCaseOther
               _ -> exitEdh ets exit EdhCaseOther

    -- { prefix @< match >@ suffix } -- sub-string cut pattern
    [StmtSrc (_, ExprStmt (InfixExpr ">@" (InfixExpr "@<" (AttrExpr (DirectRef (NamedAttr prefixName))) matchExpr) (AttrExpr (DirectRef (NamedAttr suffixName)))))]
      -> case ctxMatch of
        EdhString !fullStr ->
          runEdhTx ets $ evalExpr matchExpr $ \ !mVal _ets ->
            edhValueStr ets (edhUltimate mVal) $ \ !mStr -> if T.null mStr
              then throwEdh ets
                            UsageError
                            "you don't use empty string for match"
              else
                let (prefix, rest) = T.breakOn mStr fullStr
                in  case T.stripPrefix mStr rest of
                      Just !suffix ->
                        branchMatched
                          [ (prefixName, EdhString prefix)
                          , (suffixName, EdhString suffix)
                          ]
                      _ -> exitEdh ets exit EdhCaseOther
        _ -> exitEdh ets exit EdhCaseOther

    -- { match >@ suffix } -- prefix cut pattern
    [StmtSrc (_, ExprStmt (InfixExpr ">@" prefixExpr (AttrExpr (DirectRef (NamedAttr suffixName)))))]
      -> case ctxMatch of
        EdhString !fullStr ->
          runEdhTx ets $ evalExpr prefixExpr $ \ !lhVal _ets ->
            edhValueStr ets (edhUltimate lhVal) $ \ !lhStr ->
              case T.stripPrefix lhStr fullStr of
                Just !suffix -> branchMatched [(suffixName, EdhString suffix)]
                _            -> exitEdh ets exit EdhCaseOther
        _ -> exitEdh ets exit EdhCaseOther

    -- { prefix @< match } -- suffix cut pattern
    [StmtSrc (_, ExprStmt (InfixExpr "@<" (AttrExpr (DirectRef (NamedAttr prefixName))) suffixExpr))]
      -> case ctxMatch of
        EdhString !fullStr ->
          runEdhTx ets $ evalExpr suffixExpr $ \ !rhVal _ets ->
            edhValueStr ets (edhUltimate rhVal) $ \ !rhStr ->
              case T.stripSuffix rhStr fullStr of
                Just !prefix -> branchMatched [(prefixName, EdhString prefix)]
                _            -> exitEdh ets exit EdhCaseOther
        _ -> exitEdh ets exit EdhCaseOther

    -- {( x,y,z,... )} -- pattern matching number of positional args
    [StmtSrc (_, ExprStmt (ArgsPackExpr !argSenders))] -> if null argSenders
      then case ctxMatch of
                                                              -- an empty apk pattern matches any empty sequence
        EdhArgsPack (ArgsPack [] !kwargs) | odNull kwargs -> branchMatched []
        EdhList (List _ !l) ->
          readTVar l
            >>= \ll -> if null ll
                  then branchMatched []
                  else exitEdh ets exit EdhCaseOther
        _ -> exitEdh ets exit EdhCaseOther
      else do
        attrNames <- fmap catMaybes $ sequence $ (<$> argSenders) $ \case
          SendPosArg (AttrExpr (DirectRef (NamedAttr vAttr))) ->
            return $ Just vAttr
          _ -> return Nothing
        if length attrNames /= length argSenders
          then throwEdh
            ets
            UsageError
            ("invalid element in apk pattern: " <> T.pack (show argSenders))
          else case ctxMatch of
            EdhArgsPack (ArgsPack !args !kwargs)
              | length args == length argSenders && odNull kwargs -> branchMatched
              $ zip attrNames args
            _ -> exitEdh ets exit EdhCaseOther

    -- {{ class:inst }} -- instance resolving pattern
    [StmtSrc (_, ExprStmt (DictExpr [(AddrDictKey !clsAddr, AttrExpr (DirectRef (NamedAttr instAttr)))]))]
      -> -- brittany insists on putting together the long line above, any workaround?
         case ctxMatch of
        EdhObject ctxObj ->
          runEdhTx ets $ evalAttrAddr clsAddr $ \ !clsVal _ets -> case clsVal of
            EdhNil            -> exitEdh ets exit EdhCaseOther
            EdhObject !clsObj -> resolveEdhInstance clsObj ctxObj >>= \case
              Just instObj -> branchMatched [(instAttr, EdhObject instObj)]
              Nothing      -> exitEdh ets exit EdhCaseOther
            _ ->
              throwEdh ets EvalError
                $  T.pack
                $  "invalid class "
                <> show clsAddr
                <> ", it is a "
                <> edhTypeNameOf clsVal
                <> ": "
                <> show clsVal
        _ -> exitEdh ets exit EdhCaseOther

    -- {[ x,y,z,... ]} -- any-of pattern
    [StmtSrc (_, ExprStmt (ListExpr vExprs))] -> if null vExprs
      then exitEdh ets exit EdhCaseOther
      else runEdhTx ets $ evalExprs vExprs $ \ !matchVals _ets ->
        case matchVals of
          EdhArgsPack (ArgsPack !l _) -> if ctxMatch `elem` l
            then branchMatched []
            else exitEdh ets exit EdhCaseOther
          _ -> error "bug: evalExprs returned non-apk"


    -- TODO more kinds of match patterns to support ?
    --      e.g. list pattern, with rest-items repacking etc.
    _ -> throwEdh ets EvalError $ "invalid match pattern: " <> T.pack
      (show patternExpr)

  -- guarded condition, ignore match target in context, just check if the
  -- condition itself is true
  PrefixExpr Guard guardedExpr ->
    runEdhTx ets $ evalExpr guardedExpr $ \ !predValue _ets ->
      if edhDeCaseWrap predValue /= true
        then exitEdh ets exit EdhCaseOther
        else branchMatched []

  -- value-wise matching against the target in context
  _ -> runEdhTx ets $ evalExpr lhExpr $ \ !lhVal _ets ->
    edhNamelyEqual ets (edhDeCaseWrap lhVal) ctxMatch $ \case
      True  -> branchMatched []
      False -> exitEdh ets exit EdhCaseOther

 where
  !callerCtx   = edh'context ets
  !callerScope = contextScope callerCtx
  !ctxMatch    = edh'ctx'match callerCtx
  !scopeEntity = edh'scope'entity callerScope

  updAttrs :: [(AttrKey, EdhValue)] -> STM ()
  updAttrs [] = -- todo: which one is semantically more correct ?
    -- to trigger a write, or avoid the write
    return ()  -- this avoids triggering stm write
  updAttrs !ps' = iopdUpdate ps' scopeEntity

  branchMatched :: [(AttrName, EdhValue)] -> STM ()
  branchMatched !ps = do
    updAttrs [ (AttrByName n, noneNil v) | (n, v) <- ps, n /= "_" ]
    runEdhTx ets $ evalExpr rhExpr $ \ !rhVal -> exitEdhTx exit $ case rhVal of
      -- a nested branch matched, the outer branch eval to its final
      -- value with case closed
      EdhCaseClose !nestedMatch -> EdhCaseClose $ edhDeCaseWrap nestedMatch
      -- a nested branch mismatched, while the outer branch did match,
      -- so eval to nil with case closed
      EdhCaseOther              -> EdhCaseClose nil
      -- propagate an explicit fallthrough
      EdhFallthrough            -> EdhFallthrough
      -- some other value, the outer branch eval to it
      _                         -> EdhCaseClose rhVal

  handlePairPattern !maybeName1 !pairPattern =
    case matchPairPattern pairPattern ctxMatch [] of
      Nothing -> throwEdh ets EvalError $ "invalid pair pattern: " <> T.pack
        (show pairPattern)
      Just (_, []) -> -- valid pattern, no match
        exitEdh ets exit EdhCaseOther
      Just (resi, mps) -> case maybeName1 of
        Just !name1 -> case resi of
          Nothing    -> exitEdh ets exit EdhCaseOther
          Just !val1 -> branchMatched $ (name1, val1) : mps
        Nothing -> case resi of
          Nothing -> branchMatched mps
          Just{}  -> exitEdh ets exit EdhCaseOther

  -- | `Nothing` means invalid pattern, `[]` means no match, non-empty list is
  -- the aligned values along with attr names as matched
  matchPairPattern
    :: Expr
    -> EdhValue
    -> [(AttrName, EdhValue)]
    -> Maybe (Maybe EdhValue, [(AttrName, EdhValue)])
  matchPairPattern !p !v !matches = case p of
    AttrExpr (DirectRef (NamedAttr !lastAttr)) -> case v of
      EdhPair !resi !lastVal ->
        Just (Just resi, (lastAttr, lastVal) : matches)
      _ -> Just (Nothing, (lastAttr, v) : matches)
    InfixExpr ":" !leftExpr (AttrExpr (DirectRef (NamedAttr !vAttr))) ->
      case v of
        EdhPair !leftVal !val ->
          let matches' = (vAttr, val) : matches
          in  case leftExpr of
                (AttrExpr (DirectRef (NamedAttr !leftAttr))) ->
                  case leftVal of
                    EdhPair !resi !lastVal ->
                      Just (Just resi, (leftAttr, lastVal) : matches')
                    _ -> Just (Nothing, (leftAttr, leftVal) : matches')
                InfixExpr ":" _ _ ->
                  matchPairPattern leftExpr leftVal matches'
                _ -> Nothing
        _ -> Just (Nothing, [])
    _ -> Nothing
