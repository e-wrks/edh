
module Language.Edh.Batteries.Assign where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.Reader

import           Control.Concurrent.STM

import qualified Data.Text                     as T

import qualified Data.HashMap.Strict           as Map
import           Data.List.NonEmpty             ( (<|) )

import           Language.Edh.Control
import           Language.Edh.Runtime


-- | operator (=)
assignProc :: EdhProcedure
assignProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit = do
  pgs <- ask
  case lhExpr of
    IndexExpr ixExpr tgtExpr ->
      evalExpr ixExpr $ \(OriginalValue !ixVal _ _) ->
        -- indexing assignment
        evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
          evalExpr tgtExpr $ \(OriginalValue !tgtVal _ _) -> case tgtVal of

            -- indexing assign to a dict
            EdhDict (Dict _ !d) -> contEdhSTM $ do
              modifyTVar' d $ setDictItem ixVal rhVal
              exitEdhSTM pgs exit rhVal

            -- indexing assign to an object, by calling its ([=]) method with ixVal and rhVal
            -- as the args
            EdhObject obj ->
              contEdhSTM
                $   resolveEdhObjAttr pgs obj (AttrByName "[=]")
                >>= \case
                      Nothing ->
                        throwEdhSTM pgs EvalError
                          $  "No ([=]) method from: "
                          <> T.pack (show obj)
                      Just (OriginalValue (EdhMethod mth'proc) _ mth'that) ->
                        case procedure'body $ procedure'decl mth'proc of

                          -- calling a host method procedure
                          Right !hp -> do
                            -- a host procedure runs against its caller's scope, with
                            -- 'thatObject' changed to the resolution target object
                            let
                              !ctx         = edh'context pgs
                              !scope       = contextScope ctx
                              !calleeScope = scope { thatObject = mth'that
                                                   , scopeProc  = mth'proc
                                                   }
                              !calleeCtx = ctx
                                { callStack       = calleeScope <| callStack ctx
                                , generatorCaller = Nothing
                                , contextMatch    = true
                                }
                              !pgsCallee = pgs { edh'context = calleeCtx }
                            -- insert a cycle tick here, so if no tx required for the call
                            -- overall, the callee resolution tx stops here then the callee
                            -- runs in next stm transaction
                            flip (exitEdhSTM' pgsCallee) (wuji pgsCallee)
                              $ \_ ->
                                  hp
                                      [ SendPosArg (GodSendExpr ixVal)
                                      , SendPosArg (GodSendExpr rhVal)
                                      ]
                                    $ \(OriginalValue !val _ _) ->
                                    -- return the result in CPS with caller pgs restored
                                        contEdhSTM $ exitEdhSTM pgs exit val

                          Left !pb -> runEdhProg pgs $ callEdhMethod
                            (ArgsPack [ixVal, rhVal] Map.empty)
                            mth'that
                            mth'proc
                            pb
                            Nothing
                            exit

                      Just (OriginalValue !badIndexer _ _) ->
                        throwEdhSTM pgs EvalError
                          $  "Malformed index method ([=]) on "
                          <> T.pack (show obj)
                          <> " - "
                          <> T.pack (show $ edhTypeOf badIndexer)
                          <> ": "
                          <> T.pack (show badIndexer)

            _ ->
              throwEdh EvalError
                $  "Don't know how to index assign "
                <> T.pack (show $ edhTypeOf tgtVal)
                <> ": "
                <> T.pack (show tgtVal)
                <> " with "
                <> T.pack (show $ edhTypeOf ixVal)
                <> ": "
                <> T.pack (show ixVal)

    _ -> -- non-indexing assignment
      -- execution of the assignment always in a tx for atomicity
      local (const pgs { edh'in'tx = True })
        $ evalExpr rhExpr
        $ \(OriginalValue !rhVal _ _) -> assignEdhTarget pgs lhExpr exit rhVal

assignProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)

