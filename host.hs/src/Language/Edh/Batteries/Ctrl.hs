module Language.Edh.Batteries.Ctrl where

-- import           Debug.Trace
-- import           System.IO.Unsafe

import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception
  ( Exception (fromException, toException),
    SomeException,
  )
import Data.Dynamic (fromDynamic)
import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Unique (newUnique)
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Control
import Language.Edh.CoreLang
import Language.Edh.Evaluate
import Language.Edh.IOPD (iopdUpdate, odEmpty, odNull)
import Language.Edh.RtTypes
import Prelude

-- | operator (=:) and (::) - attribute prototype/type annotation
--
-- this should have lowest possible precedence and do nothing when eval'ed
-- so an arbitrary expression, so long as it's syntactically correct,
-- can be placed anywhere serving annotation purpose e.g.
--
--   abs :: ( Decimal ) -> Decimal
--   method abs( n ) n<0 &> ( -n ) |> n
--
--   x :: String
--   x =: 'Hello'
--
-- Currently els doesn't understand (::), while it thinks rhs of (=:) is a
-- valid value expression as if assigned to its lhs attribute addressor, for
-- sake of static analysis
attrAnnoProc :: EdhIntrinsicOp
attrAnnoProc _ _ !exit = exitEdhTx exit nil

-- | operator (:=:) - type synonym annotation
--
-- this should have lowest possible precedence and do nothing when eval'ed
-- so an arbitrary expression, so long as it's syntactically correct,
-- can be placed anywhere serving annotation purpose e.g.
--
--   CntCallback :=: ( int!Decimal ) -> nil
--   countdown :: (int!Decimal, CntCallback) -> nil
--   method countdown( fromNum, cb ) {
--     for n from range(fromNum:0:-1) do cb(n)
--   }
typeAnnoProc :: EdhIntrinsicOp
typeAnnoProc _ _ !exit = exitEdhTx exit nil

-- | operator (!) - free-form lhs annotation
--
-- left-hand-side expression is for static analysing tools only, right-hand
-- expression takes full effect, e.g.
--
--   `js!expr {value: 5}`
--
-- can be used to tell the analyzer that the expression is gonna be executed
-- by a JavaScript interpreter.
lhsFreeFormAnnoProc :: EdhIntrinsicOp
lhsFreeFormAnnoProc _ !rhExpr !exit = evalExprSrc rhExpr exit

-- | error(***) - throw an @Exception@
--
-- this being a host procedure so the tip context statement carries the
-- right Edh source location reporting the error
errorProc :: ArgsPack -> EdhHostProc
errorProc !apk _ !ets =
  edh'exception'wrapper
    (edh'prog'world $ edh'thread'prog ets)
    (toException edhErr)
    >>= \ !exo -> edhThrow ets $ EdhObject exo
  where
    !edhErr = edhCreateError 1 ets EdhException apk

-- | operator ($=>) - the `catch`
--
-- - the right-hand-expr will only be eval'ed  when an exception occurred
--   in its left-hand-expr;
-- - the exception value is the context match target during eval of the
--   right-hand-expr;
-- - the exceptin is assused to have been recovered, if the rhe evals as
--   matched (i.e. not to a value of <fallthrough>), or the exception will
--   keep propagating, i.e. re-thrown.
--
-- - especially note any asynchronous exception occurred on some descendant
--   thread forked by the @tryExpr@ will trigger the right-hand-expr to be
--   executed on that thread
catchProc :: EdhIntrinsicOp
catchProc !tryExpr !catchExpr !exit !etsOuter = do
  !handlerThId <- unsafeIOToSTM myThreadId
  edhCatch etsOuter (evalExprSrc tryExpr) (exitEdh etsOuter exit) $
    \ !etsThrower !exv recover rethrow -> do
      !throwerThId <- unsafeIOToSTM myThreadId
      let !isThreadTerminate = case exv of
            EdhObject !exo -> case edh'obj'store exo of
              HostStore !hsd -> case fromDynamic hsd of
                Just (e :: SomeException) -> case fromException e of
                  Just ThreadTerminate -> True
                  _ -> False
                _ -> False
              _ -> False
            _ -> False
      if throwerThId /= handlerThId && isThreadTerminate
        then rethrow exv -- ThreadTerminate not to cross thread boundaries
        else case exv of
          EdhNil -> rethrow nil -- no exception has occurred, no catch
          _ ->
            -- eval the catch expression to see if it recovers or not
            let !ctxOuter = edh'context etsOuter
                !ctxHndl = ctxOuter {edh'ctx'match = exv}
                !etsHndl = etsThrower {edh'context = ctxHndl}
             in runEdhTx etsHndl $
                  evalExprSrc catchExpr $
                    \ !catchResult _ets -> case edhDeCaseClose catchResult of
                      -- these results all mean no recovery, i.e. to rethrow
                      EdhRethrow -> rethrow exv -- explicit rethrow
                      EdhFallthrough -> rethrow exv -- explicit fallthrough
                      EdhCaseOther -> rethrow exv -- implicit none-match

                      -- other results are regarded as valid recovery
                      -- note `nil` included
                      !recoverVal -> recover recoverVal

-- | operator (@=>) - the `finally`
--
-- - the right-hand-expr will always be eval'ed whether the left-hand-expr
--   has caused exeption or not;
-- - the exception value (or nil if none occurred) is the context match
--   target during eval of the right-hand-expr;
-- - an exception if occurred, will never be assumed as recovered by the
--   right-hand-expr.
--
-- - especially note asynchronous exceptions won't trigger the right-hand-expr
--   to be executed
finallyProc :: EdhIntrinsicOp
finallyProc !tryExpr !finallyExpr !exit !etsOuter = do
  !handlerThId <- unsafeIOToSTM myThreadId
  edhCatch etsOuter (evalExprSrc tryExpr) (exitEdh etsOuter exit) $
    \ !etsThrower !exv _recover !rethrow -> do
      !throwerThId <- unsafeIOToSTM myThreadId
      -- note we deliberately avoid executing a finally block on a
      -- descendant thread here
      if throwerThId /= handlerThId
        then -- not on same thread, bypass finally block
          rethrow exv
        else -- on the same thread, eval the finally block

          let !ctxOuter = edh'context etsOuter
              !ctxHndl = ctxOuter {edh'ctx'match = exv}
              !etsHndl = etsThrower {edh'context = ctxHndl}
           in runEdhTx etsHndl $
                evalExprSrc finallyExpr $ \_result _ets ->
                  rethrow exv

-- | operator (=>) - arrow, define an anonymous, bound method
--
-- similar to fat arrow in JavaScript
arrowProc :: EdhIntrinsicOp
arrowProc (ExprSrc !lhExpr !lhSpan) (ExprSrc !rhExpr !rhSpan) !exit !ets =
  methodArrowArgsReceiver (deParen'1 lhExpr) $ \case
    Left !err -> throwEdh ets UsageError err
    Right !argsRcvr -> do
      !idProc <- unsafeIOToSTM newUnique
      let !pd =
            ProcDecl
              ( AttrAddrSrc
                  (NamedAttr arrowName)
                  (SrcRange (src'end lhSpan) (src'start rhSpan))
              )
              argsRcvr
              (StmtSrc (ExprStmt rhExpr Nothing) rhSpan)
              (edh'exe'src'loc tip)
                { src'range = SrcRange (src'start lhSpan) (src'end rhSpan)
                }
          !mth =
            procType
              ProcDefi
                { edh'procedure'ident = idProc,
                  edh'procedure'name = AttrByName arrowName,
                  edh'procedure'lexi = scope,
                  edh'procedure'doc = Nothing,
                  edh'procedure'decl = pd
                }
          !boundMth =
            EdhBoundProc
              mth
              (edh'scope'this scope)
              (edh'scope'that scope)
              Nothing
      exitEdh ets exit boundMth
  where
    {- HLINT ignore "Reduce duplication" -}
    !ctx = edh'context ets
    !tip = edh'ctx'tip ctx
    !scope = edh'frame'scope tip
    !arrowName = "<arrow>"

    -- to be a generator if there's a yield somewhere, or to be a vanilla method
    procType :: ProcDefi -> EdhProcDefi
    procType = if containsYield rhExpr then EdhGnrtor else EdhMethod

    containsYield :: Expr -> Bool
    containsYield YieldExpr {} = True
    containsYield (ParenExpr (ExprSrc !x _)) = containsYield x
    containsYield (BlockExpr !bs) = blockContainsYield bs
    containsYield (ScopedBlockExpr !bs) = blockContainsYield bs
    containsYield (AtoIsoExpr (ExprSrc !x _)) = containsYield x
    containsYield (PrefixExpr _ (ExprSrc !x _)) = containsYield x
    containsYield (IfExpr (ExprSrc !cnd _) !csq !alt) =
      containsYield cnd || blockContainsYield [csq] || case alt of
        Nothing -> False
        Just !body -> blockContainsYield [body]
    containsYield (CaseExpr (ExprSrc !t _) (ExprSrc !x _)) =
      containsYield t || containsYield x
    containsYield (ForExpr _ _ (ExprSrc !x _) !b) =
      containsYield x || blockContainsYield [b]
    containsYield (WhileExpr (ExprSrc !cnd _) !body) =
      containsYield cnd || blockContainsYield [body]
    containsYield (DoWhileExpr !body (ExprSrc !cnd _)) =
      containsYield cnd || blockContainsYield [body]
    containsYield (IndexExpr (ExprSrc !t _) (ExprSrc !x _)) =
      containsYield t || containsYield x
    containsYield (CallExpr (ExprSrc !x _) _) = containsYield x
    containsYield (InfixExpr _ (ExprSrc !l _) (ExprSrc !r _)) =
      containsYield l || containsYield r
    containsYield _ = False

    blockContainsYield :: [StmtSrc] -> Bool
    blockContainsYield [] = False
    blockContainsYield (StmtSrc !stmt _ : rest) = case stmt of
      ExprStmt !x _docCmt -> containsYield x || blockContainsYield rest
      _ -> blockContainsYield rest

methodArrowArgsReceiver ::
  Expr ->
  (Either Text ArgsReceiver -> STM ()) ->
  STM ()
methodArrowArgsReceiver
  (AttrExpr (DirectRef argAttr@(AttrAddrSrc !addr _)))
  !exit = case addr of
    NamedAttr "_" -> exit $ Right $ SingleReceiver $ RecvRestPkArgs argAttr
    _ -> exit $ Right $ SingleReceiver $ RecvArg argAttr Nothing Nothing
methodArrowArgsReceiver (ArgsPackExpr (ArgsPacker !argSndrs _)) !exit =
  cnvrt argSndrs []
  where
    cnvrt :: [ArgSender] -> [ArgReceiver] -> STM ()
    cnvrt [] !rcvrs = exit $ Right $ PackReceiver $ reverse rcvrs
    cnvrt (sndr : rest) !rcvrs = case sndr of
      UnpackPosArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt rest (RecvRestPosArgs argRef : rcvrs)
      UnpackKwArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt rest (RecvRestKwArgs argRef : rcvrs)
      UnpackPkArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt rest (RecvRestPkArgs argRef : rcvrs)
      SendPosArg (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt rest (RecvArg argRef Nothing Nothing : rcvrs)
      SendKwArg !argRef !defExpr ->
        cnvrt rest (RecvArg argRef Nothing (Just defExpr) : rcvrs)
      !badSndr ->
        exit $
          Left $
            "invalid argument expr for arrow: " <> T.pack (show badSndr)
methodArrowArgsReceiver !badArgs !exit =
  exit $ Left $ "invalid argument expr for arrow: " <> T.pack (show badArgs)

-- | operator (=>*) - producing arrow, define an anonymous, bound producer
prodArrowProc :: EdhIntrinsicOp
prodArrowProc (ExprSrc !lhExpr !lhSpan) (ExprSrc !rhExpr !rhSpan) !exit !ets =
  producerArrowArgsReceiver (deParen'1 lhExpr) $ \case
    Left !err -> throwEdh ets UsageError err
    Right !argsRcvr -> do
      !idProc <- unsafeIOToSTM newUnique
      let !pd =
            ProcDecl
              ( AttrAddrSrc
                  (NamedAttr arrowName)
                  (SrcRange (src'end lhSpan) (src'start rhSpan))
              )
              argsRcvr
              (StmtSrc (ExprStmt rhExpr Nothing) rhSpan)
              (edh'exe'src'loc tip)
                { src'range = SrcRange (src'start lhSpan) (src'end rhSpan)
                }
          !mth =
            EdhPrducr
              ProcDefi
                { edh'procedure'ident = idProc,
                  edh'procedure'name = AttrByName arrowName,
                  edh'procedure'lexi = scope,
                  edh'procedure'doc = Nothing,
                  edh'procedure'decl = pd
                }
          !boundMth =
            EdhBoundProc
              mth
              (edh'scope'this scope)
              (edh'scope'that scope)
              Nothing
      exitEdh ets exit boundMth
  where
    !ctx = edh'context ets
    !tip = edh'ctx'tip ctx
    !scope = edh'frame'scope tip
    !arrowName = "<producer>"

producerArrowArgsReceiver ::
  Expr ->
  (Either Text ArgsReceiver -> STM ()) ->
  STM ()
producerArrowArgsReceiver (AttrExpr (DirectRef !argAttr)) !exit =
  exit $ Right $ SingleReceiver $ RecvArg argAttr Nothing Nothing
producerArrowArgsReceiver (ArgsPackExpr (ArgsPacker !argSndrs _)) !exit =
  cnvrt False argSndrs []
  where
    cnvrt :: Bool -> [ArgSender] -> [ArgReceiver] -> STM ()
    cnvrt !outletPrsnt [] !rcvrs =
      if outletPrsnt
        then exit $ Right $ PackReceiver $ reverse rcvrs
        else
          exit $
            Right $
              PackReceiver $
                reverse
                  $! RecvArg
                    (AttrAddrSrc (NamedAttr "outlet") noSrcRange)
                    (Just (DirectRef (AttrAddrSrc (NamedAttr "_") noSrcRange)))
                    (Just (ExprSrc (LitExpr SinkCtor) noSrcRange)) :
                rcvrs
    cnvrt !outletPrsnt (sndr : rest) !rcvrs = case sndr of
      UnpackPosArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt outletPrsnt rest (RecvRestPosArgs argRef : rcvrs)
      UnpackKwArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt outletPrsnt rest (RecvRestKwArgs argRef : rcvrs)
      UnpackPkArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt outletPrsnt rest (RecvRestPkArgs argRef : rcvrs)
      SendPosArg (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt outletPrsnt rest (RecvArg argRef Nothing Nothing : rcvrs)
      SendKwArg argRef@(AttrAddrSrc !argAttr _) !defExpr ->
        cnvrt
          (outletPrsnt || argAttr == NamedAttr "outlet")
          rest
          (RecvArg argRef Nothing (Just defExpr) : rcvrs)
      !badSndr ->
        exit $
          Left $
            "invalid argument expr for arrow: " <> T.pack (show badSndr)
producerArrowArgsReceiver !badArgs !exit =
  exit $ Left $ "invalid argument expr for arrow: " <> T.pack (show badArgs)

-- | operator (->) - the brancher, if its left-hand matches, early stop its
-- enclosing code block (commonly a case-of block, but other blocks as well),
-- with eval-ed result of its right-hand, unless the right-hand result is
-- `fallthrough`
branchProc :: EdhIntrinsicOp
branchProc (ExprSrc !lhExpr _) (ExprSrc !rhExpr _) !exit !ets = case lhExpr of
  -- recognize `_` as similar to the wildcard pattern match in Haskell,
  -- it always matches
  AttrExpr (DirectRef (AttrAddrSrc (NamedAttr "_") _)) -> afterMatch
  InfixExpr ("|", _) (ExprSrc !matchExpr _) (ExprSrc !guardExpr _) ->
    handlePattern matchExpr (valueMatch matchExpr $ chkGuard guardExpr) $
      \ !ps -> do
        updAttrs ps
        chkGuard guardExpr
  _ -> handlePattern lhExpr (valueMatch lhExpr afterMatch) $ \ !ps -> do
    updAttrs ps
    afterMatch
  where
    !callerCtx = edh'context ets
    !callerScope = contextScope callerCtx
    !ctxMatch = edh'ctx'match callerCtx
    !scopeEntity = edh'scope'entity callerScope

    afterMatch :: STM ()
    afterMatch = runEdhTx ets $
      evalExpr rhExpr $ \ !rhVal ->
        exitEdhTx exit $ case rhVal of
          -- a nested branch matched, the outer branch eval to its final
          -- value with case closed
          EdhCaseClose !nestedMatch -> EdhCaseClose $ edhDeCaseWrap nestedMatch
          -- a nested branch mismatched, while the outer branch did match,
          -- so eval to nil with case closed
          EdhCaseOther -> EdhCaseClose nil
          -- propagate an explicit fallthrough
          EdhFallthrough -> EdhFallthrough
          -- some other value, the outer branch eval to it
          _ -> EdhCaseClose rhVal

    chkGuard :: Expr -> STM ()
    chkGuard !guardExpr =
      runEdhTx ets $
        evalExpr guardExpr $ \ !guardResult _ets ->
          case edhUltimate guardResult of
            EdhBool True -> afterMatch
            EdhBool False -> exitEdh ets exit EdhCaseOther
            _ -> edhValueDesc ets guardResult $ \ !badDesc ->
              throwEdh ets UsageError $ "bad guard result: " <> badDesc

    -- value-wise matching against the target in context
    valueMatch !matchExpr !matchExit =
      runEdhTx ets $
        evalExpr matchExpr $ \ !matchVal _ets ->
          edhNamelyEqual ets (edhDeCaseWrap matchVal) ctxMatch $ \case
            True -> matchExit
            False -> exitEdh ets exit EdhCaseOther

    updAttrs :: [(AttrKey, EdhValue)] -> STM ()
    updAttrs [] =
      -- todo: which one is semantically more correct ?
      -- to trigger a write, or avoid the write
      return () -- this avoids triggering stm write
    updAttrs !ps' =
      iopdUpdate
        [(k, noneNil v) | (k, v) <- ps', k /= AttrByName "_"]
        scopeEntity

    handlePattern ::
      Expr ->
      STM () ->
      ([(AttrKey, EdhValue)] -> STM ()) ->
      STM ()
    -- TODO support nested patterns
    handlePattern !fullExpr !naExit !matchExit = case fullExpr of
      BlockExpr !patternExpr -> case patternExpr of
        -- { val } -- wild capture pattern, used to capture a non-nil result as
        -- an attribute.
        -- Note: a raw nil value should be value-matched explicitly
        [ StmtSrc
            (ExprStmt (AttrExpr (DirectRef (AttrAddrSrc !valAttr _))) _docCmt)
            _
          ] ->
            case ctxMatch of -- don't match raw nil here,
              EdhNil -> exitEdh ets exit EdhCaseOther
              -- but a named nil (i.e. None/Nothing etc.) should be matched
              _ -> resolveEdhAttrAddr ets valAttr $
                \ !valKey -> matchExit [(valKey, ctxMatch)]
        --

        -- { class( field1, field2, ... ) } -- fields by class pattern
        -- __match__ magic from the class works here
        [ StmtSrc
            (ExprStmt (CallExpr (ExprSrc (AttrExpr !clsRef) _) !apkr) _docCmt)
            _
          ] ->
            dcFieldsExtractor apkr $ \ !fieldExtractors ->
              runEdhTx ets $
                evalAttrRef clsRef $ \ !clsVal _ets -> case clsVal of
                  EdhObject !clsObj ->
                    matchDataClass clsObj fieldExtractors Nothing
                  !badClsVal -> edhValueRepr ets badClsVal $ \ !badDesc ->
                    throwEdh ets UsageError $ "invalid class: " <> badDesc
        -- { class( field1, field2, ... ) = instAddr } -- fields by class again
        -- but receive the matched object as well
        -- __match__ magic from the class works here
        [ StmtSrc
            ( ExprStmt
                ( InfixExpr
                    ("=", _)
                    (ExprSrc (CallExpr (ExprSrc (AttrExpr !clsRef) _) !apkr) _)
                    (ExprSrc (AttrExpr (DirectRef (AttrAddrSrc !instAddr _))) _)
                  )
                _docCmt
              )
            _
          ] ->
            dcFieldsExtractor apkr $ \ !fieldExtractors ->
              runEdhTx ets $
                evalAttrRef clsRef $ \ !clsVal _ets -> case clsVal of
                  EdhObject !clsObj -> case instAddr of
                    NamedAttr "_" ->
                      matchDataClass clsObj fieldExtractors Nothing
                    _ -> resolveEdhAttrAddr ets instAddr $ \ !instKey ->
                      matchDataClass clsObj fieldExtractors $ Just instKey
                  !badClsVal -> edhValueRepr ets badClsVal $ \ !badDesc ->
                    throwEdh ets UsageError $ "invalid class: " <> badDesc
        -- {{ class:inst }} -- instance resolving pattern
        [ StmtSrc
            ( ExprStmt
                ( DictExpr
                    [ ( AddrDictKey !clsRef,
                        ExprSrc
                          (AttrExpr (DirectRef (AttrAddrSrc !instAttr _)))
                          _
                        )
                      ]
                  )
                _docCmt
              )
            _
          ] ->
            case ctxMatch of
              EdhObject ctxObj -> resolveEdhAttrAddr ets instAttr $
                \ !instKey -> runEdhTx ets $
                  evalAttrRef clsRef $ \ !clsVal _ets -> case clsVal of
                    EdhNil -> exitEdh ets exit EdhCaseOther
                    EdhObject !clsObj ->
                      resolveEdhInstance clsObj ctxObj >>= \case
                        Just !instObj ->
                          matchExit [(instKey, EdhObject instObj)]
                        Nothing -> exitEdh ets exit EdhCaseOther
                    !badClsVal -> edhValueRepr ets badClsVal $ \ !badDesc ->
                      throwEdh ets UsageError $ "invalid class: " <> badDesc
              _ -> exitEdh ets exit EdhCaseOther
        --

        -- {[ x,y,z,... ]} -- any-of pattern
        [StmtSrc (ExprStmt (ListExpr !vExprs) _docCmt) _] ->
          if null vExprs
            then exitEdh ets exit EdhCaseOther
            else runEdhTx ets $
              evalExprs vExprs $ \ !matchVals _ets ->
                case matchVals of
                  EdhArgsPack (ArgsPack !l _) ->
                    if ctxMatch `elem` l
                      then matchExit []
                      else exitEdh ets exit EdhCaseOther
                  _ -> error "bug: evalExprs returned non-apk"
        --

        -- { head :> tail } -- uncons pattern
        [ StmtSrc
            ( ExprStmt
                ( InfixExpr
                    (":>", _)
                    ( ExprSrc
                        ( AttrExpr
                            (DirectRef (AttrAddrSrc (NamedAttr !headName) _))
                          )
                        _
                      )
                    ( ExprSrc
                        ( AttrExpr
                            (DirectRef (AttrAddrSrc (NamedAttr !tailName) _))
                          )
                        _
                      )
                  )
                _docCmt
              )
            _
          ] ->
            let doMatched headVal tailVal =
                  matchExit
                    [ (AttrByName headName, headVal),
                      (AttrByName tailName, tailVal)
                    ]
             in case ctxMatch of
                  EdhArgsPack (ArgsPack (h : rest) !kwargs)
                    | odNull kwargs ->
                      doMatched h (EdhArgsPack (ArgsPack rest kwargs))
                  EdhList (List _ !l) ->
                    readTVar l >>= \case
                      (h : rest) -> do
                        rl <- newTVar rest
                        u <- unsafeIOToSTM newUnique
                        doMatched h $ EdhList $ List u rl
                      _ -> exitEdh ets exit EdhCaseOther
                  _ -> exitEdh ets exit EdhCaseOther
        --

        -- { prefix @< match >@ suffix } -- sub-string cut pattern
        [ StmtSrc
            ( ExprStmt
                ( InfixExpr
                    (">@", _)
                    ( ExprSrc
                        ( InfixExpr
                            ("@<", _)
                            ( ExprSrc
                                ( AttrExpr
                                    ( DirectRef
                                        (AttrAddrSrc (NamedAttr !prefixName) _)
                                      )
                                  )
                                _
                              )
                            !matchExpr
                          )
                        _
                      )
                    ( ExprSrc
                        ( AttrExpr
                            (DirectRef (AttrAddrSrc (NamedAttr !suffixName) _))
                          )
                        _
                      )
                  )
                _docCmt
              )
            _
          ] ->
            case ctxMatch of
              EdhString !fullStr ->
                runEdhTx ets $
                  evalExprSrc matchExpr $ \ !mVal _ets ->
                    edhValueStr ets (edhUltimate mVal) $ \ !mStr ->
                      if T.null mStr
                        then
                          throwEdh
                            ets
                            UsageError
                            "you don't use empty string for match"
                        else
                          let (prefix, rest) = T.breakOn mStr fullStr
                           in case T.stripPrefix mStr rest of
                                Just !suffix ->
                                  matchExit
                                    [ (AttrByName prefixName, EdhString prefix),
                                      (AttrByName suffixName, EdhString suffix)
                                    ]
                                _ -> exitEdh ets exit EdhCaseOther
              _ -> exitEdh ets exit EdhCaseOther
        -- { match >@ suffix } -- prefix cut pattern
        [ StmtSrc
            ( ExprStmt
                ( InfixExpr
                    (">@", _)
                    !prefixExpr
                    ( ExprSrc
                        ( AttrExpr
                            (DirectRef (AttrAddrSrc (NamedAttr !suffixName) _))
                          )
                        _
                      )
                  )
                _docCmt
              )
            _
          ] ->
            case ctxMatch of
              EdhString !fullStr ->
                runEdhTx ets $
                  evalExprSrc prefixExpr $ \ !lhVal _ets ->
                    edhValueStr ets (edhUltimate lhVal) $ \ !lhStr ->
                      case T.stripPrefix lhStr fullStr of
                        Just !suffix ->
                          matchExit [(AttrByName suffixName, EdhString suffix)]
                        _ -> exitEdh ets exit EdhCaseOther
              _ -> exitEdh ets exit EdhCaseOther
        -- { prefix @< match } -- suffix cut pattern
        [ StmtSrc
            ( ExprStmt
                ( InfixExpr
                    ("@<", _)
                    ( ExprSrc
                        ( AttrExpr
                            (DirectRef (AttrAddrSrc (NamedAttr !prefixName) _))
                          )
                        _
                      )
                    !suffixExpr
                  )
                _docCmt
              )
            _
          ] ->
            case ctxMatch of
              EdhString !fullStr ->
                runEdhTx ets $
                  evalExprSrc suffixExpr $ \ !rhVal _ets ->
                    edhValueStr ets (edhUltimate rhVal) $ \ !rhStr ->
                      case T.stripSuffix rhStr fullStr of
                        Just !prefix ->
                          matchExit [(AttrByName prefixName, EdhString prefix)]
                        _ -> exitEdh ets exit EdhCaseOther
              _ -> exitEdh ets exit EdhCaseOther
        --

        -- {( x )} -- single arg
        [ StmtSrc
            ( ExprStmt
                ( ParenExpr
                    ( ExprSrc
                        ( AttrExpr
                            (DirectRef (AttrAddrSrc (NamedAttr !attrName) _))
                          )
                        _
                      )
                  )
                _docCmt
              )
            _
          ] ->
            case ctxMatch of
              EdhArgsPack (ArgsPack [argVal] !kwargs)
                | odNull kwargs ->
                  matchExit [(AttrByName attrName, argVal)]
              _ -> exitEdh ets exit EdhCaseOther
        -- {( x,y,z,... )} -- pattern matching number of positional args
        [ StmtSrc
            (ExprStmt (ArgsPackExpr (ArgsPacker !argSenders _)) _docCmt)
            _
          ] ->
            if null argSenders
              then case ctxMatch of
                -- an empty apk pattern matches any empty sequence
                EdhArgsPack (ArgsPack [] !kwargs) | odNull kwargs -> matchExit []
                EdhList (List _ !l) ->
                  readTVar l
                    >>= \ll ->
                      if null ll
                        then matchExit []
                        else exitEdh ets exit EdhCaseOther
                _ -> exitEdh ets exit EdhCaseOther
              else do
                !attrNames <- fmap catMaybes $
                  sequence $
                    (<$> argSenders) $ \case
                      SendPosArg
                        ( ExprSrc
                            ( AttrExpr
                                ( DirectRef
                                    (AttrAddrSrc (NamedAttr !vAttr) _)
                                  )
                              )
                            _
                          ) ->
                          return $ Just vAttr
                      _ -> return Nothing
                if length attrNames /= length argSenders
                  then
                    throwEdh
                      ets
                      UsageError
                      ( "invalid element in apk pattern: "
                          <> T.pack (show argSenders)
                      )
                  else case ctxMatch of
                    EdhArgsPack (ArgsPack !args !kwargs)
                      | length args == length argSenders && odNull kwargs ->
                        matchExit $
                          zip (AttrByName <$> attrNames) args
                    _ -> exitEdh ets exit EdhCaseOther
        --

        -- {( x:y:z:... )} -- pair pattern
        [ StmtSrc
            ( ExprStmt
                (ParenExpr (ExprSrc pairPattern@(InfixExpr (":", _) _ _) _))
                _docCmt
              )
            _
          ] ->
            handlePairPattern Nothing pairPattern
        --

        -- { continue } -- match with continue
        [StmtSrc ContinueStmt _] -> case edhDeReturn ctxMatch of
          EdhContinue -> matchExit []
          _ -> exitEdh ets exit EdhCaseOther
        -- { break } -- match with break
        [StmtSrc BreakStmt _] -> case edhDeReturn ctxMatch of
          EdhBreak -> matchExit []
          _ -> exitEdh ets exit EdhCaseOther
        -- { fallthrough } -- match with fallthrough
        [StmtSrc FallthroughStmt _] -> case edhDeReturn ctxMatch of
          EdhFallthrough -> matchExit []
          _ -> exitEdh ets exit EdhCaseOther
        -- { return <attr> } -- capture return value
        [ StmtSrc
            ( ReturnStmt
                ( ExprSrc
                    ( AttrExpr
                        (DirectRef (AttrAddrSrc (NamedAttr !valueName) _))
                      )
                    _
                  )
                _docCmt
              )
            _
          ] -> case ctxMatch of
            EdhReturn !rtnVal ->
              matchExit [(AttrByName valueName, noneNil rtnVal)]
            _ -> exitEdh ets exit EdhCaseOther
        -- { return <expr> } -- match with expected return value
        [StmtSrc (ReturnStmt !expectExpr _docCmt) _] -> case ctxMatch of
          EdhReturn !rtnVal -> runEdhTx ets $
            evalExprSrc expectExpr $ \ !expectVal _ets ->
              edhNamelyEqual ets expectVal rtnVal $ \case
                True -> matchExit []
                False -> exitEdh ets exit EdhCaseOther
          _ -> exitEdh ets exit EdhCaseOther
        --

        -- { term := value } -- definition pattern
        [ StmtSrc
            ( ExprStmt
                ( InfixExpr
                    (":=", _)
                    ( ExprSrc
                        ( AttrExpr
                            (DirectRef (AttrAddrSrc (NamedAttr !termName) _))
                          )
                        _
                      )
                    ( ExprSrc
                        ( AttrExpr
                            (DirectRef (AttrAddrSrc (NamedAttr !valueName) _))
                          )
                        _
                      )
                  )
                _docCmt
              )
            _
          ] ->
            case ctxMatch of
              EdhNamedValue !n !v ->
                matchExit
                  [(AttrByName termName, EdhString n), (AttrByName valueName, v)]
              _ -> exitEdh ets exit EdhCaseOther
        --

        -- TODO more kinds of match patterns to support ?
        --      e.g. list pattern, with rest-items repacking etc.
        _ ->
          throwEdh ets EvalError $
            "invalid match pattern: "
              <> T.pack
                (show patternExpr)
      --

      -- guarded condition, ignore match target in context, just check if the
      -- condition expression evals to true or false
      PrefixExpr Guard !condExpr ->
        runEdhTx ets $
          evalExprSrc condExpr $ \ !guardResult _ets ->
            case edhUltimate guardResult of
              EdhBool True -> matchExit []
              EdhBool False -> exitEdh ets exit EdhCaseOther
              _ -> edhValueDesc ets guardResult $ \ !badDesc ->
                throwEdh ets UsageError $ "bad guard result: " <> badDesc
      --

      -- this is to establish the intuition that `{ ... }` always invokes
      -- pattern matching. if a literal dict value really meant to be matched,
      -- the parenthesized form `( {k1: v1, k2: v2, ...} )` should be used.
      DictExpr !malPairs ->
        throwEdh ets EvalError $
          "invalid match pattern: " <> T.pack (show malPairs)
      --

      _ -> naExit -- not a recognized pattern

      --
      where
        handlePairPattern !maybeName1 !pairPattern =
          case matchPairPattern pairPattern ctxMatch [] of
            Nothing ->
              throwEdh ets EvalError $
                "invalid pair pattern: "
                  <> T.pack
                    (show pairPattern)
            Just (_, []) ->
              -- valid pattern, no match
              exitEdh ets exit EdhCaseOther
            Just (resi, mps) -> case maybeName1 of
              Just !name1 -> case resi of
                Nothing -> exitEdh ets exit EdhCaseOther
                Just !val1 -> matchExit $ (name1, val1) : mps
              Nothing -> case resi of
                Nothing -> matchExit mps
                Just {} -> exitEdh ets exit EdhCaseOther
        matchPairPattern ::
          Expr ->
          EdhValue ->
          [(AttrKey, EdhValue)] ->
          Maybe (Maybe EdhValue, [(AttrKey, EdhValue)])
        matchPairPattern !p !v !matches = case p of
          AttrExpr (DirectRef (AttrAddrSrc (NamedAttr !lastAttr) _)) ->
            case v of
              EdhPair !resi !lastVal ->
                Just (Just resi, (AttrByName lastAttr, lastVal) : matches)
              _ -> Just (Nothing, (AttrByName lastAttr, v) : matches)
          InfixExpr
            (":", _)
            (ExprSrc !leftExpr _)
            ( ExprSrc
                ( AttrExpr
                    ( DirectRef
                        (AttrAddrSrc (NamedAttr !vAttr) _)
                      )
                  )
                _
              ) ->
              case v of
                EdhPair !leftVal !val ->
                  let matches' = (AttrByName vAttr, val) : matches
                   in case leftExpr of
                        ( AttrExpr
                            ( DirectRef
                                ( AttrAddrSrc
                                    (NamedAttr !leftAttr)
                                    _
                                  )
                              )
                          ) ->
                            case leftVal of
                              EdhPair !resi !lastVal ->
                                Just
                                  ( Just resi,
                                    (AttrByName leftAttr, lastVal) : matches'
                                  )
                              _ ->
                                Just
                                  ( Nothing,
                                    (AttrByName leftAttr, leftVal) : matches'
                                  )
                        InfixExpr (":", _) _ _ ->
                          matchPairPattern leftExpr leftVal matches'
                        _ -> Nothing
                _ -> Just (Nothing, [])
          _ -> Nothing

        dcFieldsExtractor ::
          ArgsPacker -> ([(AttrKey, AttrKey)] -> STM ()) -> STM ()
        dcFieldsExtractor (ArgsPacker !sndrs _) !exit' = go sndrs []
          where
            go [] !keys = exit' keys
            go (argSender : rest) !keys = case argSender of
              SendPosArg
                ( ExprSrc
                    ( AttrExpr
                        ( DirectRef
                            (AttrAddrSrc !rcvAttr _)
                          )
                      )
                    _
                  ) ->
                  resolveEdhAttrAddr ets rcvAttr $
                    \ !key -> go rest $ (key, key) : keys
              SendKwArg
                (AttrAddrSrc !srcAttr _)
                ( ExprSrc
                    ( AttrExpr
                        ( DirectRef
                            (AttrAddrSrc !tgtAttr _)
                          )
                      )
                    _
                  ) ->
                  resolveEdhAttrAddr ets srcAttr $ \ !srcKey ->
                    resolveEdhAttrAddr ets tgtAttr $
                      \ !tgtKey -> go rest $ (srcKey, tgtKey) : keys
              _ ->
                throwEdh ets UsageError $
                  "bad data class field extractor: "
                    <> T.pack
                      (show argSender)

        matchDataClass ::
          Object ->
          [(AttrKey, AttrKey)] ->
          Maybe AttrKey ->
          STM ()
        matchDataClass !clsObj !dcfxs !maybeInstKey =
          case edhUltimate ctxMatch of
            EdhObject !ctxObj -> withObj ctxObj tryCoerceMatch
            _ -> tryCoerceMatch
          where
            withObj !obj !alt =
              resolveEdhInstance clsObj obj >>= \case
                Just _superObj -> withMatched obj
                Nothing -> alt
            withMatched !matchedObj = go dcfxs []
              where
                go :: [(AttrKey, AttrKey)] -> [(AttrKey, EdhValue)] -> STM ()
                go [] !arts = matchExit $ case maybeInstKey of
                  Just !instKey -> arts ++ [(instKey, EdhObject matchedObj)]
                  Nothing -> arts
                go ((!srcKey, !tgtKey) : rest) !arts =
                  lookupEdhObjAttr matchedObj srcKey >>= \case
                    (_, !artVal) -> go rest $ (tgtKey, noneNil artVal) : arts

            tryCoerceMatch =
              lookupEdhObjAttr clsObj (AttrByName "__match__") >>= \case
                (_, EdhNil) -> exitEdh ets exit EdhCaseOther
                (!this', EdhProcedure (EdhMethod !mth) _) ->
                  runEdhTx ets $
                    callEdhMethod
                      this'
                      clsObj
                      mth
                      (ArgsPack [ctxMatch] odEmpty)
                      id
                      $ \ !mthRtn _ets -> case mthRtn of
                        EdhObject !obj ->
                          withObj obj $ exitEdh ets exit EdhCaseOther
                        _ -> exitEdh ets exit EdhCaseOther
                (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
                  runEdhTx ets $
                    callEdhMethod
                      this
                      that
                      mth
                      (ArgsPack [ctxMatch] odEmpty)
                      id
                      $ \ !mthRtn _ets -> case mthRtn of
                        EdhObject !obj ->
                          withObj obj $ exitEdh ets exit EdhCaseOther
                        _ -> exitEdh ets exit EdhCaseOther
                (_, !badMagic) -> edhValueDesc ets badMagic $ \ !badDesc ->
                  throwEdh ets UsageError $ "bad __match__ magic: " <> badDesc
