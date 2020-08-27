
module Language.Edh.Batteries.Assign where

import           Prelude
-- import           Debug.Trace

import           Data.Text                      ( Text )
import qualified Data.Text                     as T

import           Language.Edh.Control
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.Evaluate


-- | operator (=)
assignProc :: EdhIntrinsicOp
assignProc !lhExpr !rhExpr !exit !ets =
  runEdhTx ets {
            -- execution of the assignment always in a tx for atomicity
                 edh'in'tx   = True
            -- discourage artifact definition during assignment
               , edh'context = (edh'context ets) { edh'ctx'pure = True }
               }

    $ case lhExpr of
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
              EdhObject obj ->
                lookupEdhObjAttr obj (AttrByName "[=]") >>= \case
                  (_, EdhNil) ->
                    throwEdh ets EvalError
                      $  "no magic ([=]) method from: "
                      <> T.pack (show obj)
                  (this', EdhProcedure (EdhMethod !mth'proc) _) ->
                    -- enforced tx boundary cut just before
                    -- magic method call, after args prepared
                    runEdhTx ets $ callEdhMethod
                      this'
                      obj
                      mth'proc
                      (ArgsPack [ixVal, rhv] odEmpty)
                      id
                      exit
                  (_, EdhBoundProc (EdhMethod !mth'proc) !this !that _) ->
                    -- enforced tx boundary cut just before
                    -- magic method call, after args prepared
                    runEdhTx ets $ callEdhMethod
                      this
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

              _ ->
                throwEdh ets EvalError
                  $  "don't know how to index assign "
                  <> T.pack (edhTypeNameOf tgtVal)
                  <> ": "
                  <> T.pack (show tgtVal)
                  <> " with "
                  <> T.pack (edhTypeNameOf ixVal)
                  <> ": "
                  <> T.pack (show ixVal)

        _ -> evalExpr rhExpr $ \ !rhVal ->
          assignEdhTarget lhExpr (edhDeCaseWrap rhVal)
            -- restore original tx state
            $ edhSwitchState ets
            . exitEdhTx exit


-- | operator (+=), (-=), (*=), (/=), (//=), (&&=), (||=) etc.
assignWithOpProc :: Text -> EdhIntrinsicOp -> EdhIntrinsicOp
assignWithOpProc !withOpSym !withOp !lhExpr !rhExpr !exit !ets =
  runEdhTx ets {
            -- execution of the assignment always in a tx for atomicity
                 edh'in'tx   = True
            -- discourage artifact definition during assignment
               , edh'context = (edh'context ets) { edh'ctx'pure = True }
               }

    $ case lhExpr of
        IndexExpr ixExpr tgtExpr -> evalExpr ixExpr $ \ !ixV -> do
          let !ixVal = edhDeCaseWrap ixV
          evalExpr rhExpr $ \ !rhVal -> do
            let !rhv = edhDeCaseWrap rhVal
            evalExpr tgtExpr $ \ !tgtVal !ets' -> case edhUltimate tgtVal of

              -- indexing assign to a dict
              EdhDict (Dict _ !ds) ->
                iopdLookupDefault EdhNil ixVal ds >>= \ !dVal ->
                  runEdhTx ets'
                    $ withOp (IntplSubs dVal) (IntplSubs rhv)
                    $ \ !opRtnV _ets -> do
                        case opRtnV of
                          EdhDefault{} -> pure ()
                          _            -> setDictItem ixVal opRtnV ds
                        -- restore original tx state
                        exitEdh ets exit opRtnV

              -- indexing assign to an object, by calling its ([op=])
              EdhObject obj -> -- method with ixVal and rhv as the args
                lookupEdhObjAttr obj (AttrByName magicMthName) >>= \case
                  (_, EdhNil) ->
                    throwEdh ets EvalError
                      $  "no magic ("
                      <> magicMthName
                      <> ") method from: "
                      <> T.pack (show obj)
                  (!this', EdhProcedure (EdhMethod !mth'proc) _) ->
                    -- enforced tx boundary cut just before
                    -- magic method call, after args prepared
                    runEdhTx ets $ callEdhMethod
                      this'
                      obj
                      mth'proc
                      (ArgsPack [ixVal, rhv] odEmpty)
                      id
                      exit
                  (_, EdhBoundProc (EdhMethod !mth'proc) !this !that _) ->
                    -- enforced tx boundary cut just before
                    -- magic method call, after args prepared
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

              _ ->
                throwEdh ets EvalError
                  $  "don't know how to index assign "
                  <> T.pack (edhTypeNameOf tgtVal)
                  <> ": "
                  <> T.pack (show tgtVal)
                  <> " with "
                  <> T.pack (edhTypeNameOf ixVal)
                  <> ": "
                  <> T.pack (show ixVal)

        _ -> evalExpr rhExpr $ \ !rhVal -> evalExpr lhExpr $ \ !lhVal ->
          withOp (IntplSubs lhVal) (IntplSubs $ edhDeCaseWrap rhVal)
            $ \ !opRtnV -> case edhUltimate opRtnV of
                EdhDefault{} -> edhSwitchState ets $ exitEdhTx exit opRtnV
                _ -> assignEdhTarget lhExpr opRtnV $ edhSwitchState ets . exit
  where magicMthName = "[" <> withOpSym <> "=]"


-- | operator (?=)
assignMissingProc :: EdhIntrinsicOp
assignMissingProc (AttrExpr (DirectRef (NamedAttr "_"))) _ _ !ets =
  throwEdh ets UsageError "not so reasonable: _ ?= xxx"
assignMissingProc (AttrExpr (DirectRef !addr)) !rhExpr !exit !ets =
  resolveEdhAttrAddr ets addr $ \ !key -> do
    let !es = edh'scope'entity $ contextScope $ edh'context ets
    iopdLookup key es >>= \case
      Nothing ->
        runEdhTx ets {
            -- execution of the assignment always in a tx for atomicity
                       edh'in'tx   = True
            -- discourage artifact definition during assignment
                     , edh'context = (edh'context ets) { edh'ctx'pure = True }
                     }
          $ evalExpr rhExpr
          $ \ !rhVal _ets ->
              let !rhv = edhDeCaseWrap rhVal
              in  do
                    edhSetValue key rhv es
                    exitEdh ets exit rhv
      Just !preVal -> exitEdh ets exit preVal
assignMissingProc !lhExpr _ _ !ets =
  throwEdh ets EvalError $ "invalid left-hand expression to (?=) " <> T.pack
    (show lhExpr)

