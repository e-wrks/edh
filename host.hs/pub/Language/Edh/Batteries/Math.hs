
module Language.Edh.Batteries.Math where

import           Prelude
-- import           Debug.Trace

import           Data.Lossless.Decimal

import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate

import           Language.Edh.Batteries.Data


-- | operator (+)
addProc :: EdhIntrinsicOp
addProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum + rhNum)
        _                 -> concatProc (LitExpr (ValueLiteral lhVal))
                                        (LitExpr (ValueLiteral rhVal))
                                        exit
    _ -> concatProc (LitExpr (ValueLiteral lhVal)) rhExpr exit


-- | operator (-)
subtProc :: EdhIntrinsicOp
subtProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
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
      Nothing   -> exitEdhTx exit edhNA
      Just !lhi -> evalExpr rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing -> exitEdhTx exit edhNA
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
      Nothing  -> exitEdhTx exit edhNA
      Just lhi -> evalExpr rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing  -> exitEdhTx exit edhNA
          Just rhi -> exitEdhTx exit $ EdhDecimal $ Decimal 1 0 $ lhi `mod` rhi
        _ -> exitEdhTx exit edhNA
    _ -> exitEdhTx exit edhNA


-- | operator (**)
powProc :: EdhIntrinsicOp
powProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExpr rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum ->
          exitEdhTx exit (EdhDecimal $ powerDecimal lhNum rhNum)
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


-- | operator (==) and (!=)
valEqProc :: (Bool -> Bool) -> EdhIntrinsicOp
valEqProc !inversion !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr $ \ !rhVal !ets -> if lhVal == rhVal
    then case lhVal of
      EdhObject{} -> -- same object, give default result, so magic enabled,
         -- vectorized equality test to itself is possible
        exitEdh ets exit =<< mkDefault (LitExpr $ BoolLiteral $ inversion True)
      _ -> -- identity equal and not an object, can conclude value equal here
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
idEqProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal -> evalExpr rhExpr
  $ \ !rhVal -> exitEdhTx exit (EdhBool $ edhIdentEqual lhVal rhVal)

-- | operator (is not)
idNotEqProc :: EdhIntrinsicOp
idNotEqProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr
    $ \ !rhVal -> exitEdhTx exit (EdhBool $ not $ edhIdentEqual lhVal rhVal)


-- | operator (>)
isGtProc :: EdhIntrinsicOp
isGtProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr $ \ !rhVal -> doEdhComparison' exit lhVal rhVal $ \case
    GT -> True
    _  -> False

-- | operator (>=)
isGeProc :: EdhIntrinsicOp
isGeProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr $ \ !rhVal -> doEdhComparison' exit lhVal rhVal $ \case
    GT -> True
    EQ -> True
    _  -> False

-- | operator (<)
isLtProc :: EdhIntrinsicOp
isLtProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr $ \ !rhVal -> doEdhComparison' exit lhVal rhVal $ \case
    LT -> True
    _  -> False

-- | operator (<=)
isLeProc :: EdhIntrinsicOp
isLeProc !lhExpr !rhExpr !exit = evalExpr lhExpr $ \ !lhVal ->
  evalExpr rhExpr $ \ !rhVal -> doEdhComparison' exit lhVal rhVal $ \case
    LT -> True
    EQ -> True
    _  -> False

doEdhComparison'
  :: EdhTxExit -> EdhValue -> EdhValue -> (Ordering -> Bool) -> EdhTx
doEdhComparison' !exit !lhVal !rhVal !cm !ets =
  doEdhComparison ets lhVal rhVal $ \case
    Nothing   -> exitEdh ets exit edhNA
    Just !ord -> exitEdh ets exit $ EdhBool $ cm ord

