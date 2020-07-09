
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
        EdhDecimal !rhNum -> exitEdhProc exit (EdhDecimal $ lhNum + rhNum)
        _                 -> exitEdhProc exit EdhContinue
    EdhBlob !lhb -> evalExpr rhExpr $ \(OriginalValue !rhv _ _) ->
      case edhUltimate rhv of
        EdhBlob   !rhb -> exitEdhProc exit (EdhBlob $ lhb <> rhb)
        EdhString !rhs -> exitEdhProc exit (EdhBlob $ lhb <> TE.encodeUtf8 rhs)
        rhVal ->
          throwEdh UsageError
            $  "Should not (+) a "
            <> T.pack (edhTypeNameOf rhVal)
            <> " to a blob."
    EdhString !lhs -> evalExpr rhExpr $ \(OriginalValue !rhv _ _) ->
      edhValueStr (edhUltimate rhv) $ \(OriginalValue rhStr _ _) ->
        case rhStr of
          EdhString !rhs -> exitEdhProc exit (EdhString $ lhs <> rhs)
          _              -> error "bug: edhValueStr returned non-string"
    _ -> exitEdhProc exit EdhContinue


-- | operator (-)
subsProc :: EdhIntrinsicOp
subsProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhProc exit (EdhDecimal $ lhNum - rhNum)
        _                 -> exitEdhProc exit EdhContinue
    _ -> exitEdhProc exit EdhContinue


-- | operator (*)
mulProc :: EdhIntrinsicOp
mulProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhProc exit (EdhDecimal $ lhNum * rhNum)
        _                 -> exitEdhProc exit EdhContinue
    _ -> exitEdhProc exit EdhContinue


-- | operator (/)
divProc :: EdhIntrinsicOp
divProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhProc exit (EdhDecimal $ lhNum / rhNum)
        _                 -> exitEdhProc exit EdhContinue
    _ -> exitEdhProc exit EdhContinue

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
              exitEdhProc exit $ EdhDecimal $ Decimal 1 0 $ lhi `div` rhi
          _ -> exitEdhProc exit EdhContinue
    _ -> exitEdhProc exit EdhContinue

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
              exitEdhProc exit $ EdhDecimal $ Decimal 1 0 $ lhi `mod` rhi
          _ -> exitEdhProc exit EdhContinue
    _ -> exitEdhProc exit EdhContinue


-- | operator (**)
powProc :: EdhIntrinsicOp
powProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal (Decimal rh'd rh'e rh'n) -> if rh'd /= 1
          then exitEdhProc exit EdhContinue
          else exitEdhProc exit (EdhDecimal $ lhNum ^^ (rh'n * 10 ^ rh'e))
        _ -> exitEdhProc exit EdhContinue
    _ -> exitEdhProc exit EdhContinue


-- | operator (&&)
logicalAndProc :: EdhIntrinsicOp
logicalAndProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhBool lhBool -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhBool rhBool -> exitEdhProc exit (EdhBool $ lhBool && rhBool)
        _              -> exitEdhProc exit EdhContinue
    _ -> exitEdhProc exit EdhContinue

-- | operator (||)
logicalOrProc :: EdhIntrinsicOp
logicalOrProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhBool lhBool -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhBool rhBool -> exitEdhProc exit (EdhBool $ lhBool || rhBool)
        _              -> exitEdhProc exit EdhContinue
    _ -> exitEdhProc exit EdhContinue


-- | operator (==)
valEqProc :: EdhIntrinsicOp
valEqProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ edhValueEqual pgs lhVal rhVal $ \case
        Just !conclusion -> exitEdhSTM pgs exit $ EdhBool conclusion
        -- allow magic methods to be invoked
        Nothing          -> exitEdhSTM pgs exit EdhContinue

-- | operator (!=)
idNeProc :: EdhIntrinsicOp
idNeProc !lhExpr !rhExpr !exit = ask >>= \ !pgs ->
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ edhValueEqual pgs lhVal rhVal $ \case
        Just !conclusion -> exitEdhSTM pgs exit $ EdhBool $ not conclusion
        -- allow magic methods to be invoked
        Nothing          -> exitEdhSTM pgs exit EdhContinue

-- | operator (is)
idEqProc :: EdhIntrinsicOp
idEqProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      exitEdhProc exit (EdhBool $ edhIdentEqual lhVal rhVal)

-- | operator (is not) (not is)
idNotEqProc :: EdhIntrinsicOp
idNotEqProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      exitEdhProc exit (EdhBool $ not $ edhIdentEqual lhVal rhVal)


-- | operator (>)
isGtProc :: EdhIntrinsicOp
isGtProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ doEdhComparison pgs exit lhVal rhVal $ \case
        GT -> True
        _  -> False

-- | operator (>=)
isGeProc :: EdhIntrinsicOp
isGeProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ doEdhComparison pgs exit lhVal rhVal $ \case
        GT -> True
        EQ -> True
        _  -> False

-- | operator (<)
isLtProc :: EdhIntrinsicOp
isLtProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ doEdhComparison pgs exit lhVal rhVal $ \case
        LT -> True
        _  -> False

-- | operator (<=)
isLeProc :: EdhIntrinsicOp
isLeProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ doEdhComparison pgs exit lhVal rhVal $ \case
        LT -> True
        EQ -> True
        _  -> False


doEdhComparison
  :: EdhProgState
  -> EdhProcExit
  -> EdhValue
  -> EdhValue
  -> (Ordering -> Bool)
  -> STM ()
doEdhComparison pgs exit lhVal rhVal cm = compareEdhValue lhVal rhVal >>= \case
  Nothing  -> exitEdhSTM pgs exit EdhContinue
  Just ord -> exitEdhSTM pgs exit (EdhBool $ cm ord)

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

