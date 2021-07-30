module Language.Edh.Batteries.Assign where

-- import           Debug.Trace

import qualified Data.Text as T
import Language.Edh.Control
import Language.Edh.CoreLang
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.RtTypes
import Prelude

-- | operator (=), unconditional assignment
assignProc :: EdhIntrinsicOp
assignProc (ExprSrc !lhe _) !rhExpr !exit !ets =
  runEdhTx etsAssign $ case lhe of
    -- indexing assignment
    IndexExpr !ixExpr !tgtExpr -> evalExprSrc ixExpr $ \ !ixV -> do
      let !ixVal = edhDeCaseWrap ixV
      evalExprSrc rhExpr $ \ !rhVal -> do
        let !rhv = edhDeCaseWrap rhVal
        evalExprSrc tgtExpr $ \ !tgtVal _ets -> case edhUltimate tgtVal of
          -- indexing assign to a dict
          EdhDict (Dict _ !ds) -> do
            setDictItem ixVal rhv ds
            exitEdh ets exit rhv

          -- indexing assign to an object, by calling its ([=])
          -- method with ixVal and rhv as the args
          EdhObject obj ->
            lookupEdhObjAttr obj (AttrByName "([=])") >>= \case
              (_, EdhNil) -> exitEdh ets exit edhNA
              (this', EdhProcedure (EdhMethod !mth'proc) _) ->
                runEdhTx ets $
                  callEdhMethod
                    this'
                    obj
                    mth'proc
                    (ArgsPack [ixVal, rhv] odEmpty)
                    id
                    exit
              (_, EdhBoundProc (EdhMethod !mth'proc) !this !that _) ->
                runEdhTx ets $
                  callEdhMethod
                    this
                    that
                    mth'proc
                    (ArgsPack [ixVal, rhv] odEmpty)
                    id
                    exit
              (_, !badIndexer) ->
                throwEdh ets EvalError $
                  "malformed magic method ([=]) on "
                    <> T.pack (show obj)
                    <> " - "
                    <> edhTypeNameOf badIndexer
                    <> ": "
                    <> T.pack (show badIndexer)
          _ -> exitEdh ets exit edhNA
    _ -> evalExprSrc rhExpr $ \ !rhVal ->
      assignEdhTarget lhe (edhDeCaseWrap rhVal) $
        -- restore original tx state
        -- wrap with the sacred return to cease defaulting semantics
        edhSwitchState ets . exitEdhTx exit . EdhReturn . EdhReturn
  where
    -- discourage artifact definition during assignment
    !etsAssign = ets {edh'context = (edh'context ets) {edh'ctx'pure = True}}

-- | operator (+=), (-=), (*=), (/=), (//=), (&&=), (||=) etc.
assignWithOpProc :: OpSymbol -> EdhIntrinsicOp
assignWithOpProc !withOpSym lhExpr@(ExprSrc !lhe _) !rhExpr !exit !ets =
  runEdhTx etsAssign $ case lhe of
    IndexExpr !ixExpr !tgtExpr -> evalExprSrc ixExpr $ \ !ixV -> do
      let !ixVal = edhDeCaseWrap ixV
      evalExprSrc rhExpr $ \ !rhVal -> do
        let !rhv = edhDeCaseWrap rhVal
        evalExprSrc tgtExpr $ \ !tgtVal _ets -> case edhUltimate tgtVal of
          -- indexing assign to a dict
          EdhDict (Dict _ !ds) ->
            iopdLookupDefault EdhNil ixVal ds >>= \ !dVal ->
              runEdhTx ets $
                evalInfix
                  withOpSym
                  (LitExpr $ ValueLiteral dVal)
                  (LitExpr $ ValueLiteral rhv)
                  $ \ !opRtnV _ets -> do
                    case opRtnV of
                      EdhDefault {} -> pure ()
                      _ -> setDictItem ixVal opRtnV ds
                    -- restore original tx state
                    exitEdh ets exit opRtnV

          -- indexing assign to an object, by calling its ([op=]) method
          -- with ixVal and rhv as the args
          EdhObject obj ->
            let !magicMthName = "([" <> withOpSym <> "=])"
             in lookupEdhObjAttr obj (AttrByName magicMthName) >>= \case
                  (_, EdhNil) -> exitEdh ets exit edhNA
                  (!this', EdhProcedure (EdhMethod !mth'proc) _) ->
                    runEdhTx ets $
                      callEdhMethod
                        this'
                        obj
                        mth'proc
                        (ArgsPack [ixVal, rhv] odEmpty)
                        id
                        exit
                  (_, EdhBoundProc (EdhMethod !mth'proc) !this !that _) ->
                    runEdhTx ets $
                      callEdhMethod
                        this
                        that
                        mth'proc
                        (ArgsPack [ixVal, rhv] odEmpty)
                        id
                        exit
                  (_, !badIndexer) ->
                    throwEdh ets EvalError $
                      "malformed magic method "
                        <> magicMthName
                        <> " on "
                        <> T.pack (show obj)
                        <> " - "
                        <> edhTypeNameOf badIndexer
                        <> ": "
                        <> T.pack (show badIndexer)
          _ -> exitEdh ets exit edhNA
    _ -> evalExprSrc rhExpr $ \ !rhVal -> evalExprSrc lhExpr $ \ !lhVal -> do
      let lhMagicMthName = "(" <> withOpSym <> "=)"
          rhMagicMthName = "(" <> withOpSym <> "=.)"
          tryRightHandMagic !rhObj =
            lookupEdhObjAttr rhObj (AttrByName rhMagicMthName) >>= \case
              (_, EdhNil) -> exitEdh ets exit edhNA
              (!this', EdhProcedure (EdhMethod !mth'proc) _) ->
                runEdhTx ets $
                  callEdhMethod
                    this'
                    rhObj
                    mth'proc
                    (ArgsPack [lhVal] odEmpty)
                    id
                    exit
              (_, EdhBoundProc (EdhMethod !mth'proc) !this !that _) ->
                runEdhTx ets $
                  callEdhMethod
                    this
                    that
                    mth'proc
                    (ArgsPack [lhVal] odEmpty)
                    id
                    exit
              (_, !badIndexer) ->
                throwEdh ets EvalError $
                  "malformed magic method ("
                    <> lhMagicMthName
                    <> ") on "
                    <> T.pack (show rhObj)
                    <> " - "
                    <> edhTypeNameOf badIndexer
                    <> ": "
                    <> T.pack (show badIndexer)

      case edhUltimate lhVal of
        EdhObject !lhObj -> \_ets ->
          lookupEdhObjAttr lhObj (AttrByName lhMagicMthName) >>= \case
            (_, EdhNil) -> case edhUltimate rhVal of
              EdhObject !rhObj -> tryRightHandMagic rhObj
              _ -> exitEdh ets exit edhNA
            (!this', EdhProcedure (EdhMethod !mth'proc) _) ->
              runEdhTx ets $
                callEdhMethod
                  this'
                  lhObj
                  mth'proc
                  (ArgsPack [rhVal] odEmpty)
                  id
                  exit
            (_, EdhBoundProc (EdhMethod !mth'proc) !this !that _) ->
              runEdhTx ets $
                callEdhMethod
                  this
                  that
                  mth'proc
                  (ArgsPack [rhVal] odEmpty)
                  id
                  exit
            (_, !badIndexer) ->
              throwEdh ets EvalError $
                "malformed magic method ("
                  <> lhMagicMthName
                  <> ") on "
                  <> T.pack (show lhObj)
                  <> " - "
                  <> edhTypeNameOf badIndexer
                  <> ": "
                  <> T.pack (show badIndexer)
        _ -> case edhUltimate rhVal of
          EdhObject !rhObj -> \_ets -> tryRightHandMagic rhObj
          _ ->
            evalInfix
              withOpSym
              (LitExpr $ ValueLiteral lhVal)
              (LitExpr $ ValueLiteral $ edhDeCaseWrap rhVal)
              $ \ !opRtnV -> case edhUltimate opRtnV of
                EdhDefault {} -> edhSwitchState ets $ exitEdhTx exit opRtnV
                _ ->
                  assignEdhTarget lhe opRtnV $
                    -- wrap with the sacred return to cease defaulting semantics
                    edhSwitchState ets . exit . EdhReturn . EdhReturn
  where
    -- discourage artifact definition during assignment
    !etsAssign = ets {edh'context = (edh'context ets) {edh'ctx'pure = True}}

-- | operator (?=), tentative assignment
assignMissingProc :: EdhIntrinsicOp
assignMissingProc
  (ExprSrc (AttrExpr (DirectRef (AttrAddrSrc (NamedAttr "_") _))) _)
  _
  _
  !ets =
    throwEdh ets UsageError "not so reasonable: _ ?= xxx"
assignMissingProc
  (ExprSrc (AttrExpr (DirectRef (AttrAddrSrc !addr _))) _)
  !rhExpr
  !exit
  !ets =
    resolveEdhAttrAddr ets addr $ \ !key -> do
      let !es = edh'scope'entity $ contextScope $ edh'context ets
      iopdLookup key es >>= \case
        Nothing -> do
          -- discourage artifact definition during assignment
          let !etsAssign =
                ets {edh'context = (edh'context ets) {edh'ctx'pure = True}}
          runEdhTx etsAssign $
            evalExprSrc rhExpr $ \ !rhVal _ets ->
              let !rhv = edhDeCaseWrap rhVal
               in do
                    edhSetValue key rhv es
                    -- wrap with the sacred return to cease defaulting semantics
                    exitEdh ets exit $ EdhReturn $ EdhReturn rhv
        Just !preVal ->
          -- wrap with the sacred return to cease defaulting semantics
          exitEdh ets exit $ EdhReturn $ EdhReturn preVal
assignMissingProc !lhExpr _ _ !ets =
  throwEdh ets EvalError $
    "invalid left-hand expression to (?=) " <> T.pack (show lhExpr)

-- | operator (|=), null overwritting assignment
overwriteNullProc :: EdhIntrinsicOp
overwriteNullProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal !ets ->
  edhValueNull ets lhVal $ \case
    False ->
      -- wrap with the sacred return to cease defaulting semantics
      exitEdh ets exit $ EdhReturn $ EdhReturn lhVal
    True ->
      runEdhTx ets $
        assignProc assignTgtExpr rhExpr $
          edhSwitchState ets . exitEdhTx exit
  where
    assignTgtExpr = case lhExpr of
      ExprSrc
        ( InfixExpr
            (OpSymSrc "?" _)
            !owner
            (ExprSrc (AttrExpr (DirectRef !addr)) _)
          )
        !expr'span -> ExprSrc (AttrExpr $ IndirectRef owner addr) expr'span
      _ -> lhExpr
