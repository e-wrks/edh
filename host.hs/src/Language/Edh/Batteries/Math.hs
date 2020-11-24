module Language.Edh.Batteries.Math where

-- import           Debug.Trace

import Data.Lossless.Decimal
  ( Decimal (Decimal),
    decimalToInteger,
    powerDecimal,
  )
import Language.Edh.Batteries.Data (concatProc)
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.RtTypes
import Prelude

-- | operator (+)
addProc :: EdhIntrinsicOp
addProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum + rhNum)
        _ ->
          concatProc
            (ExprSrc (LitExpr (ValueLiteral lhVal)) noSrcRange)
            (ExprSrc (LitExpr (ValueLiteral rhVal)) noSrcRange)
            exit
    _ ->
      concatProc
        (ExprSrc (LitExpr (ValueLiteral lhVal)) noSrcRange)
        rhExpr
        exit

-- | operator (-)
subtProc :: EdhIntrinsicOp
subtProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum - rhNum)
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (*)
mulProc :: EdhIntrinsicOp
mulProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum * rhNum)
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (/)
divProc :: EdhIntrinsicOp
divProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum / rhNum)
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (//) integer division, following Python
-- http://python-history.blogspot.com/2010/08/why-pythons-integer-division-floors.html
divIntProc :: EdhIntrinsicOp
divIntProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing -> exitEdhTx exit edhNA
      Just !lhi -> evalExprSrc rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing -> exitEdhTx exit edhNA
          Just !rhi ->
            exitEdhTx exit $ EdhDecimal $ Decimal 1 0 $ lhi `div` rhi
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (%) modulus of integer division, following Python
-- http://python-history.blogspot.com/2010/08/why-pythons-integer-division-floors.html
modIntProc :: EdhIntrinsicOp
modIntProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing -> exitEdhTx exit edhNA
      Just lhi -> evalExprSrc rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing -> exitEdhTx exit edhNA
          Just rhi -> exitEdhTx exit $ EdhDecimal $ Decimal 1 0 $ lhi `mod` rhi
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (**)
powProc :: EdhIntrinsicOp
powProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum ->
          exitEdhTx exit (EdhDecimal $ powerDecimal lhNum rhNum)
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (and)
nullishAndProc :: EdhIntrinsicOp
nullishAndProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal !ets ->
  edhValueNull ets lhVal $ \case
    -- short-circuiting, avoid eval of rhe
    True -> exitEdh ets exit lhVal
    -- give right-hand value out
    False -> runEdhTx ets $ evalExprSrc rhExpr exit

-- | operator (or)
nullishOrProc :: EdhIntrinsicOp
nullishOrProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal !ets ->
  edhValueNull ets lhVal $ \case
    -- short-circuiting, avoid eval of rhe
    False -> exitEdh ets exit lhVal
    -- give right-hand value out
    True -> runEdhTx ets $ evalExprSrc rhExpr exit

-- | operator (&&)
logicalAndProc :: EdhIntrinsicOp
logicalAndProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhBool lhBool -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhBool rhBool -> exitEdhTx exit (EdhBool $ lhBool && rhBool)
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (||)
logicalOrProc :: EdhIntrinsicOp
logicalOrProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhBool lhBool -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhBool rhBool -> exitEdhTx exit (EdhBool $ lhBool || rhBool)
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA

-- | operator (==) and (!=)
valEqProc :: (Bool -> Bool) -> EdhIntrinsicOp
valEqProc !inversion !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $ \ !rhVal !ets ->
    if lhVal == rhVal
      then case lhVal of
        EdhObject {} ->
          -- same object, give default result, so magic enabled,
          -- vectorized equality test to itself is possible
          exitEdh ets exit =<< mkDefault (LitExpr $ BoolLiteral $ inversion True)
        _ ->
          -- identity equal and not an object, can conclude value equal here
          exitEdh ets exit $ EdhBool $ inversion True
      else vanillaTest ets lhVal rhVal
  where
    vanillaTest !ets !lhVal !rhVal = edhValueEqual ets lhVal rhVal $ \case
      Just !conclusion -> exitEdh ets exit $ EdhBool $ inversion conclusion
      -- allow magic methods to be invoked, but default to not equal
      Nothing ->
        exitEdh ets exit =<< mkDefault (LitExpr $ BoolLiteral $ inversion False)

-- | operator (is)
idEqProc :: EdhIntrinsicOp
idEqProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $
    \ !rhVal -> exitEdhTx exit (EdhBool $ edhIdentEqual lhVal rhVal)

-- | operator (is not)
idNotEqProc :: EdhIntrinsicOp
idNotEqProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $
    \ !rhVal -> exitEdhTx exit (EdhBool $ not $ edhIdentEqual lhVal rhVal)

-- | operator (>)
isGtProc :: EdhIntrinsicOp
isGtProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $ \ !rhVal -> edhCompareValue' exit lhVal rhVal $ \case
    GT -> True
    _ -> False

-- | operator (>=)
isGeProc :: EdhIntrinsicOp
isGeProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $ \ !rhVal -> edhCompareValue' exit lhVal rhVal $ \case
    GT -> True
    EQ -> True
    _ -> False

-- | operator (<)
isLtProc :: EdhIntrinsicOp
isLtProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $ \ !rhVal -> edhCompareValue' exit lhVal rhVal $ \case
    LT -> True
    _ -> False

-- | operator (<=)
isLeProc :: EdhIntrinsicOp
isLeProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $ \ !rhVal -> edhCompareValue' exit lhVal rhVal $ \case
    LT -> True
    EQ -> True
    _ -> False

edhCompareValue' ::
  EdhTxExit EdhValue -> EdhValue -> EdhValue -> (Ordering -> Bool) -> EdhTx
edhCompareValue' !exit !lhVal !rhVal !cm !ets =
  edhCompareValue ets lhVal rhVal $ \case
    Nothing -> exitEdh ets exit edhNA
    Just !ord -> exitEdh ets exit $ EdhBool $ cm ord
