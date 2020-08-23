
module Language.Edh.Batteries.Math where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.Reader
import           Control.Concurrent.STM

import qualified Data.Text                     as T
import qualified Data.Text.Encoding            as TE

import           Data.Lossless.Decimal

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | operator (+)
addProc :: EdhIntrinsicOp
addProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \(OriginalValue !lhv _ _) ->
  case edhUltimate lhv of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum + rhNum)
        _                 -> exitEdhTx exit EdhContinue
    EdhBlob !lhb -> evalExpr rhExpr $ \(OriginalValue !rhv _ _) ->
      case edhUltimate rhv of
        EdhBlob   !rhb -> exitEdhTx exit (EdhBlob $ lhb <> rhb)
        EdhString !rhs -> exitEdhTx exit (EdhBlob $ lhb <> TE.encodeUtf8 rhs)
        rhVal ->
          throwEdh UsageError
            $  "Should not (+) a "
            <> T.pack (edhTypeNameOf rhVal)
            <> " to a blob."
    EdhString !lhs -> evalExpr rhExpr $ \(OriginalValue !rhv _ _) ->
      edhValueStr (edhUltimate rhv) $ \(OriginalValue rhStr _ _) ->
        case rhStr of
          EdhString !rhs -> exitEdhTx exit (EdhString $ lhs <> rhs)
          _              -> error "bug: edhValueStr returned non-string"
    _ -> exitEdhTx exit EdhContinue


-- | operator (-)
subsProc :: EdhIntrinsicOp
subsProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum - rhNum)
        _                 -> exitEdhTx exit EdhContinue
    _ -> exitEdhTx exit EdhContinue


-- | operator (*)
mulProc :: EdhIntrinsicOp
mulProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum * rhNum)
        _                 -> exitEdhTx exit EdhContinue
    _ -> exitEdhTx exit EdhContinue


-- | operator (/)
divProc :: EdhIntrinsicOp
divProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum / rhNum)
        _                 -> exitEdhTx exit EdhContinue
    _ -> exitEdhTx exit EdhContinue

-- | operator (//) integer division, following Python 
-- http://python-history.blogspot.com/2010/08/why-pythons-integer-division-floors.html
divIntProc :: EdhIntrinsicOp
divIntProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing ->
        throwEdh EvalError
          $  "Not an integer as left-hand value for (//) operation: "
          <> T.pack (show lhNum)
      Just !lhi -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
        case edhUltimate rhVal of
          EdhDecimal !rhNum -> case decimalToInteger rhNum of
            Nothing ->
              throwEdh EvalError
                $  "Not an integer as right-hand value for (//) operation: "
                <> T.pack (show rhNum)
            Just !rhi ->
              exitEdhTx exit $ EdhDecimal $ Decimal 1 0 $ lhi `div` rhi
          _ -> exitEdhTx exit EdhContinue
    _ -> exitEdhTx exit EdhContinue

-- | operator (%) modulus of integer division, following Python 
-- http://python-history.blogspot.com/2010/08/why-pythons-integer-division-floors.html
modIntProc :: EdhIntrinsicOp
modIntProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing ->
        throwEdh EvalError
          $  "Not an integer as left-hand value for (%) operation: "
          <> T.pack (show lhNum)
      Just lhi -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
        case edhUltimate rhVal of
          EdhDecimal !rhNum -> case decimalToInteger rhNum of
            Nothing ->
              throwEdh EvalError
                $  "Not an integer as right-hand value for (%) operation: "
                <> T.pack (show rhNum)
            Just rhi ->
              exitEdhTx exit $ EdhDecimal $ Decimal 1 0 $ lhi `mod` rhi
          _ -> exitEdhTx exit EdhContinue
    _ -> exitEdhTx exit EdhContinue


-- | operator (**)
powProc :: EdhIntrinsicOp
powProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal (Decimal rh'd rh'e rh'n) -> if rh'd /= 1
          then exitEdhTx exit EdhContinue
          else exitEdhTx exit (EdhDecimal $ lhNum ^^ (rh'n * 10 ^ rh'e))
        _ -> exitEdhTx exit EdhContinue
    _ -> exitEdhTx exit EdhContinue


-- | operator (&&)
logicalAndProc :: EdhIntrinsicOp
logicalAndProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhBool lhBool -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhBool rhBool -> exitEdhTx exit (EdhBool $ lhBool && rhBool)
        _              -> exitEdhTx exit EdhContinue
    _ -> exitEdhTx exit EdhContinue

-- | operator (||)
logicalOrProc :: EdhIntrinsicOp
logicalOrProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhBool lhBool -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhBool rhBool -> exitEdhTx exit (EdhBool $ lhBool || rhBool)
        _              -> exitEdhTx exit EdhContinue
    _ -> exitEdhTx exit EdhContinue


-- | operator (==)
valEqProc :: EdhIntrinsicOp
valEqProc !lhExpr !rhExpr !exit = do
  !ets <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ edhValueEqual ets lhVal rhVal $ \case
        Just !conclusion -> exitEdh ets exit $ EdhBool conclusion
        -- allow magic methods to be invoked, but default to not equal
        Nothing          -> exitEdh ets exit $ EdhDefault $ EdhBool False

-- | operator (!=)
idNeProc :: EdhIntrinsicOp
idNeProc !lhExpr !rhExpr !exit = ask >>= \ !ets ->
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ edhValueEqual ets lhVal rhVal $ \case
        Just !conclusion -> exitEdh ets exit $ EdhBool $ not conclusion
        -- allow magic methods to be invoked, but default to not equal
        Nothing          -> exitEdh ets exit $ EdhDefault $ EdhBool True

-- | operator (is)
idEqProc :: EdhIntrinsicOp
idEqProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      exitEdhTx exit (EdhBool $ edhIdentEqual lhVal rhVal)

-- | operator (is not) (not is)
idNotEqProc :: EdhIntrinsicOp
idNotEqProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      exitEdhTx exit (EdhBool $ not $ edhIdentEqual lhVal rhVal)


-- | operator (>)
isGtProc :: EdhIntrinsicOp
isGtProc !lhExpr !rhExpr !exit = do
  !ets <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ doEdhComparison ets exit lhVal rhVal $ \case
        GT -> True
        _  -> False

-- | operator (>=)
isGeProc :: EdhIntrinsicOp
isGeProc !lhExpr !rhExpr !exit = do
  !ets <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ doEdhComparison ets exit lhVal rhVal $ \case
        GT -> True
        EQ -> True
        _  -> False

-- | operator (<)
isLtProc :: EdhIntrinsicOp
isLtProc !lhExpr !rhExpr !exit = do
  !ets <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ doEdhComparison ets exit lhVal rhVal $ \case
        LT -> True
        _  -> False

-- | operator (<=)
isLeProc :: EdhIntrinsicOp
isLeProc !lhExpr !rhExpr !exit = do
  !ets <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ doEdhComparison ets exit lhVal rhVal $ \case
        LT -> True
        EQ -> True
        _  -> False


doEdhComparison
  :: EdhProgState
  -> EdhTxExit
  -> EdhValue
  -> EdhValue
  -> (Ordering -> Bool)
  -> STM ()
doEdhComparison ets exit lhVal rhVal cm = compareEdhValue lhVal rhVal >>= \case
  Nothing  -> exitEdh ets exit EdhContinue
  Just ord -> exitEdh ets exit (EdhBool $ cm ord)

compareEdhValue :: EdhValue -> EdhValue -> STM (Maybe Ordering)
compareEdhValue lhVal rhVal = case edhUltimate lhVal of
  EdhDecimal !lhNum -> case edhUltimate rhVal of
    EdhDecimal !rhNum -> return $ Just $ compare lhNum rhNum
    _                 -> return Nothing
  EdhString lhStr -> case edhUltimate rhVal of
    EdhString rhStr -> return $ Just $ compare lhStr rhStr
    _               -> return Nothing
  EdhBool lhCnd -> case edhUltimate rhVal of
    EdhBool rhCnd -> return $ Just $ compare lhCnd rhCnd
    _             -> return Nothing
  _ -> return Nothing

