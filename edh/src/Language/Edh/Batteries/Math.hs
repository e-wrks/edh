
module Language.Edh.Batteries.Math where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import qualified Data.Text                     as T
import qualified Data.Text.Encoding            as TE

import           Data.Lossless.Decimal

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | operator (+)
addProc :: EdhIntrinsicOp
addProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhv ->
  case edhUltimate lhv of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum + rhNum)
        _                 -> exitEdhTx exit edhNA
    EdhBlob !lhb -> evalExpr rhExpr $ \ !rhv -> case edhUltimate rhv of
      EdhBlob   !rhb -> exitEdhTx exit (EdhBlob $ lhb <> rhb)
      EdhString !rhs -> exitEdhTx exit (EdhBlob $ lhb <> TE.encodeUtf8 rhs)
      rhVal ->
        throwEdhTx UsageError
          $  "Should not (+) a "
          <> T.pack (edhTypeNameOf rhVal)
          <> " to a blob."
    EdhString !lhs -> evalExpr rhExpr $ \ !rhv !ets ->
      edhValueStr ets (edhUltimate rhv)
        $ \ !rhs -> exitEdh ets exit (EdhString $ lhs <> rhs)
    _ -> exitEdhTx exit edhNA


-- | operator (-)
subsProc :: EdhIntrinsicOp
subsProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum - rhNum)
        _                 -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA


-- | operator (*)
mulProc :: EdhIntrinsicOp
mulProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum * rhNum)
        _                 -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA


-- | operator (/)
divProc :: EdhIntrinsicOp
divProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum / rhNum)
        _                 -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (//) integer division, following Python 
-- http://python-history.blogspot.com/2010/08/why-pythons-integer-division-floors.html
divIntProc :: EdhIntrinsicOp
divIntProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing ->
        throwEdhTx EvalError
          $  "Not an integer as left-hand value for (//) operation: "
          <> T.pack (show lhNum)
      Just !lhi -> evalExpr rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing ->
            throwEdhTx EvalError
              $  "Not an integer as right-hand value for (//) operation: "
              <> T.pack (show rhNum)
          Just !rhi ->
            exitEdhTx exit $ EdhDecimal $ Decimal 1 0 $ lhi `div` rhi
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (%) modulus of integer division, following Python 
-- http://python-history.blogspot.com/2010/08/why-pythons-integer-division-floors.html
modIntProc :: EdhIntrinsicOp
modIntProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing ->
        throwEdhTx EvalError
          $  "Not an integer as left-hand value for (%) operation: "
          <> T.pack (show lhNum)
      Just lhi -> evalExpr rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing ->
            throwEdhTx EvalError
              $  "Not an integer as right-hand value for (%) operation: "
              <> T.pack (show rhNum)
          Just rhi -> exitEdhTx exit $ EdhDecimal $ Decimal 1 0 $ lhi `mod` rhi
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA


-- | operator (**)
powProc :: EdhIntrinsicOp
powProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal (Decimal rh'd rh'e rh'n) -> if rh'd /= 1
          then exitEdhTx exit edhNA
          else exitEdhTx exit (EdhDecimal $ lhNum ^^ (rh'n * 10 ^ rh'e))
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA


-- | operator (&&)
logicalAndProc :: EdhIntrinsicOp
logicalAndProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhBool lhBool -> evalExpr rhExpr $ \ !rhVal -> case edhUltimate rhVal of
      EdhBool rhBool -> exitEdhTx exit (EdhBool $ lhBool && rhBool)
      _              -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (||)
logicalOrProc :: EdhIntrinsicOp
logicalOrProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhBool lhBool -> evalExpr rhExpr $ \ !rhVal -> case edhUltimate rhVal of
      EdhBool rhBool -> exitEdhTx exit (EdhBool $ lhBool || rhBool)
      _              -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA


-- | operator (==)
valEqProc :: EdhIntrinsicOp
valEqProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr $ \ !rhVal !ets -> edhValueEqual ets lhVal rhVal $ \case
    Just !conclusion -> exitEdh ets exit $ EdhBool conclusion
    -- allow magic methods to be invoked, but default to not equal
    Nothing -> exitEdh ets exit =<< mkDefault (LitExpr $ BoolLiteral False)

-- | operator (!=)
idNeProc :: EdhIntrinsicOp
idNeProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr $ \ !rhVal !ets -> edhValueEqual ets lhVal rhVal $ \case
    Just !conclusion -> exitEdh ets exit $ EdhBool $ not conclusion
    -- allow magic methods to be invoked, but default to not equal
    Nothing -> exitEdh ets exit =<< mkDefault (LitExpr $ BoolLiteral True)

-- | operator (is)
idEqProc :: EdhIntrinsicOp
idEqProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal -> evalExpr rhExpr
  $ \ !rhVal -> exitEdhTx exit (EdhBool $ edhIdentEqual lhVal rhVal)

-- | operator (is not) (not is)
idNotEqProc :: EdhIntrinsicOp
idNotEqProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr
    $ \ !rhVal -> exitEdhTx exit (EdhBool $ not $ edhIdentEqual lhVal rhVal)


-- | operator (>)
isGtProc :: EdhIntrinsicOp
isGtProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr $ \ !rhVal -> doEdhComparison exit lhVal rhVal $ \case
    GT -> True
    _  -> False

-- | operator (>=)
isGeProc :: EdhIntrinsicOp
isGeProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr $ \ !rhVal -> doEdhComparison exit lhVal rhVal $ \case
    GT -> True
    EQ -> True
    _  -> False

-- | operator (<)
isLtProc :: EdhIntrinsicOp
isLtProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr $ \ !rhVal -> doEdhComparison exit lhVal rhVal $ \case
    LT -> True
    _  -> False

-- | operator (<=)
isLeProc :: EdhIntrinsicOp
isLeProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr $ \ !rhVal -> doEdhComparison exit lhVal rhVal $ \case
    LT -> True
    EQ -> True
    _  -> False


doEdhComparison
  :: EdhTxExit -> EdhValue -> EdhValue -> (Ordering -> Bool) -> EdhTx
doEdhComparison !exit !lhVal !rhVal !cm !ets = compareEdhValue >>= \case
  Nothing  -> exitEdh ets exit edhNA
  Just ord -> exitEdh ets exit (EdhBool $ cm ord)
 where
  compareEdhValue :: STM (Maybe Ordering)
  compareEdhValue = case edhUltimate lhVal of
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

