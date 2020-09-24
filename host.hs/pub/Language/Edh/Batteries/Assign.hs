
module Language.Edh.Batteries.Assign where

import           Prelude
-- import           Debug.Trace

import qualified Data.Text                     as T

import           Language.Edh.Control
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.Evaluate


-- | operator (=)
assignProc :: EdhIntrinsicOp
assignProc !lhExpr !rhExpr !exit !ets = runEdhTx etsAssign $ case lhExpr of
  -- indexing assignment
  IndexExpr !ixExpr !tgtExpr -> evalExpr ixExpr $ \ !ixV -> do
    let !ixVal = edhDeCaseWrap ixV
    evalExpr rhExpr $ \ !rhVal -> do
      let !rhv = edhDeCaseWrap rhVal
      evalExpr tgtExpr $ \ !tgtVal _ets -> case edhUltimate tgtVal of

        -- indexing assign to a dict
        EdhDict (Dict _ !ds) -> do
          setDictItem ixVal rhv ds
          exitEdh ets exit rhv

        -- indexing assign to an object, by calling its ([=])
        -- method with ixVal and rhv as the args
        EdhObject obj -> lookupEdhObjAttr obj (AttrByName "[=]") >>= \case
          (_, EdhNil) -> exitEdh ets exit edhNA
          (this', EdhProcedure (EdhMethod !mth'proc) _) ->
            runEdhTx ets $ callEdhMethod this'
                                         obj
                                         mth'proc
                                         (ArgsPack [ixVal, rhv] odEmpty)
                                         id
                                         exit
          (_, EdhBoundProc (EdhMethod !mth'proc) !this !that _) ->
            runEdhTx ets $ callEdhMethod this
                                         that
                                         mth'proc
                                         (ArgsPack [ixVal, rhv] odEmpty)
                                         id
                                         exit
          (_, !badIndexer) ->
            throwEdh ets EvalError
              $  "malformed magic method ([=]) on "
              <> T.pack (show obj)
              <> " - "
              <> T.pack (edhTypeNameOf badIndexer)
              <> ": "
              <> T.pack (show badIndexer)

        _ -> exitEdh ets exit edhNA

  _ -> evalExpr rhExpr $ \ !rhVal ->
    assignEdhTarget lhExpr (edhDeCaseWrap rhVal)
      -- restore original tx state
      $ edhSwitchState ets
      . exitEdhTx exit

 where
  -- discourage artifact definition during assignment
  !etsAssign = ets { edh'context = (edh'context ets) { edh'ctx'pure = True } }


-- | operator (+=), (-=), (*=), (/=), (//=), (&&=), (||=) etc.
assignWithOpProc :: OpSymbol -> EdhIntrinsicOp
assignWithOpProc !withOpSym !lhExpr !rhExpr !exit !ets =
  runEdhTx etsAssign $ case lhExpr of
    IndexExpr ixExpr tgtExpr -> evalExpr ixExpr $ \ !ixV -> do
      let !ixVal = edhDeCaseWrap ixV
      evalExpr rhExpr $ \ !rhVal -> do
        let !rhv = edhDeCaseWrap rhVal
        evalExpr tgtExpr $ \ !tgtVal _ets -> case edhUltimate tgtVal of

          -- indexing assign to a dict
          EdhDict (Dict _ !ds) ->
            iopdLookupDefault EdhNil ixVal ds >>= \ !dVal ->
              runEdhTx ets
                $ evalInfix withOpSym
                            (LitExpr $ ValueLiteral dVal)
                            (LitExpr $ ValueLiteral rhv)
                $ \ !opRtnV _ets -> do
                    case opRtnV of
                      EdhDefault{} -> pure ()
                      _            -> setDictItem ixVal opRtnV ds
                    -- restore original tx state
                    exitEdh ets exit opRtnV

          -- indexing assign to an object, by calling its ([op=]) method
          -- with ixVal and rhv as the args
          EdhObject obj ->
            let !magicMthName = "[" <> withOpSym <> "=]"
            in  lookupEdhObjAttr obj (AttrByName magicMthName) >>= \case
                  (_, EdhNil) -> exitEdh ets exit edhNA
                  (!this', EdhProcedure (EdhMethod !mth'proc) _) ->
                    runEdhTx ets $ callEdhMethod
                      this'
                      obj
                      mth'proc
                      (ArgsPack [ixVal, rhv] odEmpty)
                      id
                      exit
                  (_, EdhBoundProc (EdhMethod !mth'proc) !this !that _) ->
                    runEdhTx ets $ callEdhMethod
                      this
                      that
                      mth'proc
                      (ArgsPack [ixVal, rhv] odEmpty)
                      id
                      exit
                  (_, !badIndexer) ->
                    throwEdh ets EvalError
                      $  "malformed magic method ("
                      <> magicMthName
                      <> ") on "
                      <> T.pack (show obj)
                      <> " - "
                      <> T.pack (edhTypeNameOf badIndexer)
                      <> ": "
                      <> T.pack (show badIndexer)

          _ -> exitEdh ets exit edhNA

    _ -> evalExpr rhExpr $ \ !rhVal -> evalExpr lhExpr $ \ !lhVal -> do
      let lhMagicMthName = withOpSym <> "="
          rhMagicMthName = withOpSym <> "=@"
          tryRightHandMagic !rhObj =
            lookupEdhObjAttr rhObj (AttrByName rhMagicMthName) >>= \case

              (_, EdhNil) -> exitEdh ets exit edhNA

              (!this', EdhProcedure (EdhMethod !mth'proc) _) ->
                runEdhTx ets $ callEdhMethod this'
                                             rhObj
                                             mth'proc
                                             (ArgsPack [lhVal] odEmpty)
                                             id
                                             exit
              (_, EdhBoundProc (EdhMethod !mth'proc) !this !that _) ->
                runEdhTx ets $ callEdhMethod this
                                             that
                                             mth'proc
                                             (ArgsPack [lhVal] odEmpty)
                                             id
                                             exit
              (_, !badIndexer) ->
                throwEdh ets EvalError
                  $  "malformed magic method ("
                  <> lhMagicMthName
                  <> ") on "
                  <> T.pack (show rhObj)
                  <> " - "
                  <> T.pack (edhTypeNameOf badIndexer)
                  <> ": "
                  <> T.pack (show badIndexer)

      case edhUltimate lhVal of

        EdhObject !lhObj -> \_ets ->
          lookupEdhObjAttr lhObj (AttrByName lhMagicMthName) >>= \case

            (_, EdhNil) -> case edhUltimate rhVal of
              EdhObject !rhObj -> tryRightHandMagic rhObj
              _                -> exitEdh ets exit edhNA


            (!this', EdhProcedure (EdhMethod !mth'proc) _) ->
              runEdhTx ets $ callEdhMethod this'
                                           lhObj
                                           mth'proc
                                           (ArgsPack [rhVal] odEmpty)
                                           id
                                           exit
            (_, EdhBoundProc (EdhMethod !mth'proc) !this !that _) ->
              runEdhTx ets $ callEdhMethod this
                                           that
                                           mth'proc
                                           (ArgsPack [rhVal] odEmpty)
                                           id
                                           exit
            (_, !badIndexer) ->
              throwEdh ets EvalError
                $  "malformed magic method ("
                <> lhMagicMthName
                <> ") on "
                <> T.pack (show lhObj)
                <> " - "
                <> T.pack (edhTypeNameOf badIndexer)
                <> ": "
                <> T.pack (show badIndexer)

        _ -> case edhUltimate rhVal of

          EdhObject !rhObj -> \_ets -> tryRightHandMagic rhObj

          _ ->
            evalInfix withOpSym
                      (LitExpr $ ValueLiteral lhVal)
                      (LitExpr $ ValueLiteral $ edhDeCaseWrap rhVal)
              $ \ !opRtnV -> case edhUltimate opRtnV of
                  EdhDefault{} -> edhSwitchState ets $ exitEdhTx exit opRtnV
                  _ ->
                    assignEdhTarget lhExpr opRtnV $ edhSwitchState ets . exit

 where
  -- discourage artifact definition during assignment
  !etsAssign = ets { edh'context = (edh'context ets) { edh'ctx'pure = True } }


-- | operator (?=)
assignMissingProc :: EdhIntrinsicOp
assignMissingProc (AttrExpr (DirectRef (NamedAttr "_"))) _ _ !ets =
  throwEdh ets UsageError "not so reasonable: _ ?= xxx"
assignMissingProc (AttrExpr (DirectRef !addr)) !rhExpr !exit !ets =
  resolveEdhAttrAddr ets addr $ \ !key -> do
    let !es = edh'scope'entity $ contextScope $ edh'context ets
    iopdLookup key es >>= \case
      Nothing -> do
        -- discourage artifact definition during assignment
        let !etsAssign =
              ets { edh'context = (edh'context ets) { edh'ctx'pure = True } }
        runEdhTx etsAssign $ evalExpr rhExpr $ \ !rhVal _ets ->
          let !rhv = edhDeCaseWrap rhVal
          in  do
                edhSetValue key rhv es
                exitEdh ets exit rhv
      Just !preVal -> exitEdh ets exit preVal
assignMissingProc !lhExpr _ _ !ets =
  throwEdh ets EvalError $ "invalid left-hand expression to (?=) " <> T.pack
    (show lhExpr)

