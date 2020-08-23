
module Language.Edh.Batteries.Assign where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.Reader

import           Data.Text                      ( Text )
import qualified Data.Text                     as T

import           Language.Edh.Control
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.Evaluate


-- | operator (=)
assignProc :: EdhIntrinsicOp
assignProc !lhExpr !rhExpr !exit = ask >>= \ !ets ->
  local
      (const ets {
            -- execution of the assignment always in a tx for atomicity
                   edh'in'tx   = True
                 , edh'context = (edh'context ets) {
            -- discourage artifact definition during assignment
                                                     contextPure = True }
                 }
      )
    $ case lhExpr of
        IndexExpr ixExpr tgtExpr -> -- indexing assignment
          evalExpr ixExpr $ \(OriginalValue !ixV _ _) -> do
            let !ixVal = edhDeCaseClose ixV
            evalExpr rhExpr $ \(OriginalValue !rhV _ _) -> do
              let !rhVal = edhDeCaseClose rhV
              evalExpr tgtExpr $ \(OriginalValue !tgtVal _ _) ->
                case edhUltimate tgtVal of

                    -- indexing assign to a dict
                  EdhDict (Dict _ !ds) -> contEdhSTM $ do
                    setDictItem ixVal rhVal ds
                    exitEdh ets exit rhVal

                  -- indexing assign to an object, by calling its ([=])
                  -- method with ixVal and rhVal as the args
                  EdhObject obj ->
                    contEdhSTM
                      $   lookupEdhObjAttr ets obj (AttrByName "[=]")
                      >>= \case
                            EdhNil ->
                              throwEdh ets EvalError
                                $  "No magic ([=]) method from: "
                                <> T.pack (show obj)
                            EdhMethod !mth'proc ->
                              -- enforced tx boundary cut just before
                              -- magic method call, after args prepared
                              runEdhTx ets $ callEdhMethod
                                obj
                                mth'proc
                                (ArgsPack [ixVal, rhVal] odEmpty)
                                id
                                exit
                            !badIndexer ->
                              throwEdh ets EvalError
                                $  "Malformed magic method ([=]) on "
                                <> T.pack (show obj)
                                <> " - "
                                <> T.pack (edhTypeNameOf badIndexer)
                                <> ": "
                                <> T.pack (show badIndexer)

                  _ ->
                    local (const ets)
                      $  throwEdh EvalError
                      $  "Don't know how to index assign "
                      <> T.pack (edhTypeNameOf tgtVal)
                      <> ": "
                      <> T.pack (show tgtVal)
                      <> " with "
                      <> T.pack (edhTypeNameOf ixVal)
                      <> ": "
                      <> T.pack (show ixVal)

        _ -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
          assignEdhTarget ets lhExpr exit $ edhDeCaseClose rhVal


-- | operator (+=), (-=), (*=), (/=), (//=), (&&=), (||=) etc.
assignWithOpProc :: Text -> EdhIntrinsicOp -> EdhIntrinsicOp
assignWithOpProc !withOpSym !withOp !lhExpr !rhExpr !exit = ask >>= \ !ets ->
  local
      (const ets {
            -- execution of the assignment always in a tx for atomicity
                   edh'in'tx   = True
                 , edh'context = (edh'context ets) {
            -- discourage artifact definition during assignment
                                                     contextPure = True }
                 }
      )
    $ case lhExpr of
        IndexExpr ixExpr tgtExpr ->
          evalExpr ixExpr $ \(OriginalValue !ixV _ _) -> do
            let !ixVal = edhDeCaseClose ixV
            evalExpr rhExpr $ \(OriginalValue !rhV _ _) -> do
              let !rhVal = edhDeCaseClose rhV
              evalExpr tgtExpr $ \(OriginalValue !tgtVal _ _) ->
                case edhUltimate tgtVal of

                  -- indexing assign to a dict
                  EdhDict (Dict _ !ds) ->
                    contEdhSTM
                      $   iopdLookupDefault EdhNil ixVal ds
                      >>= \ !dVal ->
                            runEdhTx ets
                              $ withOp (IntplSubs dVal) (IntplSubs rhVal)
                              $ \(OriginalValue !opRtnV _ _) -> contEdhSTM $ do
                                  setDictItem ixVal opRtnV ds
                                  exitEdh ets exit opRtnV

                  -- indexing assign to an object, by calling its ([op=])
                  EdhObject obj -> -- method with ixVal and rhVal as the args
                    contEdhSTM
                      $   lookupEdhObjAttr ets obj (AttrByName magicMthName)
                      >>= \case
                            EdhNil ->
                              throwEdh ets EvalError
                                $  "No magic ("
                                <> magicMthName
                                <> ") method from: "
                                <> T.pack (show obj)
                            EdhMethod !mth'proc ->
                              -- enforced tx boundary cut just before
                              -- magic method call, after args prepared
                              runEdhTx ets $ callEdhMethod
                                obj
                                mth'proc
                                (ArgsPack [ixVal, rhVal] odEmpty)
                                id
                                exit
                            !badIndexer ->
                              throwEdh ets EvalError
                                $  "Malformed magic method ("
                                <> magicMthName
                                <> ") on "
                                <> T.pack (show obj)
                                <> " - "
                                <> T.pack (edhTypeNameOf badIndexer)
                                <> ": "
                                <> T.pack (show badIndexer)

                  _ ->
                    local (const ets)
                      $  throwEdh EvalError
                      $  "Don't know how to index assign "
                      <> T.pack (edhTypeNameOf tgtVal)
                      <> ": "
                      <> T.pack (show tgtVal)
                      <> " with "
                      <> T.pack (edhTypeNameOf ixVal)
                      <> ": "
                      <> T.pack (show ixVal)

        _ -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
          evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
            withOp (IntplSubs lhVal) (IntplSubs $ edhDeCaseClose rhVal)
              $ \opRtn@(OriginalValue !opRtnV _ _) -> case edhUltimate opRtnV of
                  EdhContinue -> exitEdhTx' exit opRtn
                  !opRtnVal   -> assignEdhTarget ets lhExpr exit opRtnVal
  where magicMthName = "[" <> withOpSym <> "=]"


-- | operator (?=)
assignMissingProc :: EdhIntrinsicOp
assignMissingProc (AttrExpr (DirectRef (NamedAttr "_"))) _ _ =
  throwEdh UsageError "Not so reasonable: _ ?= xxx"
assignMissingProc (AttrExpr (DirectRef !addr)) !rhExpr !exit = ask >>= \ets ->
  contEdhSTM $ resolveEdhAttrAddr ets addr $ \key -> do
    let !ent      = scopeEntity $ contextScope $ edh'context ets
        etsAssign = ets
          {
            -- execution of the assignment always in a tx for atomicity
            edh'in'tx   = True
          , edh'context = (edh'context ets) {
            -- discourage artifact definition during assignment
                                              contextPure = True }
          }
    lookupEntityAttr etsAssign ent key >>= \case
      EdhNil ->
        runEdhTx etsAssign $ evalExpr rhExpr $ \(OriginalValue !rhV _ _) ->
          let !rhVal = edhDeCaseClose rhV
          in  contEdhSTM $ do
                changeEntityAttr etsAssign ent key rhVal
                exitEdh ets exit rhVal
      !preVal -> exitEdh ets exit preVal
assignMissingProc !lhExpr _ _ =
  throwEdh EvalError $ "Invalid left-hand expression to (?=) " <> T.pack
    (show lhExpr)

