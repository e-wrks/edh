module Language.Edh.Batteries.Math where

-- import           Debug.Trace

import Control.Concurrent.STM
import Data.Lossless.Decimal
  ( Decimal (Decimal),
    decimalToInteger,
    powerDecimal,
  )
import Language.Edh.Args
import Language.Edh.Batteries.Data
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.IOPD
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
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (*)
mulProc :: EdhIntrinsicOp
mulProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum * rhNum)
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (/)
divProc :: EdhIntrinsicOp
divProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum / rhNum)
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (//) integer division, following Python
-- http://python-history.blogspot.com/2010/08/why-pythons-integer-division-floors.html
divIntProc :: EdhIntrinsicOp
divIntProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing -> intrinsicOpReturnNA'WithLHV exit lhVal
      Just !lhi -> evalExprSrc rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing -> intrinsicOpReturnNA exit lhVal rhVal
          Just !rhi ->
            exitEdhTx exit $ EdhDecimal $ Decimal 1 0 $ lhi `div` rhi
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (%) modulus of integer division, following Python
-- http://python-history.blogspot.com/2010/08/why-pythons-integer-division-floors.html
modIntProc :: EdhIntrinsicOp
modIntProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing -> intrinsicOpReturnNA'WithLHV exit lhVal
      Just lhi -> evalExprSrc rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing -> intrinsicOpReturnNA exit lhVal rhVal
          Just rhi -> exitEdhTx exit $ EdhDecimal $ Decimal 1 0 $ lhi `mod` rhi
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (**)
powProc :: EdhIntrinsicOp
powProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum ->
          exitEdhTx exit (EdhDecimal $ powerDecimal lhNum rhNum)
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | virtual property DecimalType.trunc
--
-- truncate to integer toward zero
decTruncProc :: "d" !: Decimal -> EdhHostProc
decTruncProc (mandatoryArg -> d) !exit =
  exitEdhTx exit $ EdhDecimal $ fromInteger $ truncate d

-- | virtual property DecimalType.round
--
-- round to integer toward zero
decRoundProc :: "d" !: Decimal -> EdhHostProc
decRoundProc (mandatoryArg -> d) !exit =
  exitEdhTx exit $ EdhDecimal $ fromInteger $ round d

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
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (||)
logicalOrProc :: EdhIntrinsicOp
logicalOrProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhBool lhBool -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhBool rhBool -> exitEdhTx exit (EdhBool $ lhBool || rhBool)
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- * equality comparisons

-- | operator (==) and (!=)
valEqProc :: (Bool -> Bool) -> EdhIntrinsicOp
valEqProc !inversion !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case rhExpr of
    ExprSrc
      (InfixExpr rhSym@(opSym, _) midExpr@(ExprSrc _ mid'span) !rhExpr')
      _
        | opSym `elem` ["==", "!="] -> evalExprSrc midExpr $ \ !midVal -> do
          -- chaining equality comparisons
          -- todo support magic vectorization in this case?
          let rhCmp :: EdhTx
              rhCmp =
                evalInfixSrc
                  rhSym
                  (ExprSrc (LitExpr (ValueLiteral midVal)) mid'span)
                  rhExpr'
                  exit
          if lhVal == midVal
            then
              if inversion True
                then rhCmp
                else -- short circuit
                  exitEdhTx exit $ EdhBool False
            else \ !ets -> edhValueEqual ets lhVal midVal $ \case
              Nothing ->
                if inversion False
                  then runEdhTx ets rhCmp
                  else -- short circuit
                    exitEdh ets exit $ EdhBool False
              Just !conclusion ->
                if inversion conclusion
                  then runEdhTx ets rhCmp
                  else -- short circuit
                    exitEdh ets exit $ EdhBool False
    _ -> evalExprSrc rhExpr $ \ !rhVal !ets ->
      if lhVal == rhVal
        then case lhVal of
          EdhObject {} ->
            -- same object, give default result, so magic enabled,
            -- vectorized equality test to itself is possible
            exitEdh ets exit
              =<< mkDefault''
                Nothing
                (ArgsPack [lhVal, rhVal] odEmpty)
                (LitExpr $ BoolLiteral $ inversion True)
          _ ->
            -- identity equal and not an object, can conclude value equal here
            exitEdh ets exit $ EdhBool $ inversion True
        else vanillaTest ets lhVal rhVal
  where
    -- allow magic methods to be invoked
    vanillaTest !ets !lhVal !rhVal = edhValueEqual ets lhVal rhVal $ \case
      Just !conclusion ->
        exitEdh ets exit
          =<< mkDefault''
            Nothing
            (ArgsPack [lhVal, rhVal] odEmpty)
            (LitExpr $ BoolLiteral $ inversion conclusion)
      Nothing ->
        exitEdh ets exit
          =<< mkDefault''
            Nothing
            (ArgsPack [lhVal, rhVal] odEmpty)
            (LitExpr $ BoolLiteral $ inversion False)

-- * in range test

inRangeProc :: (Bool -> Bool) -> EdhIntrinsicOp
inRangeProc inverse !lhExpr !rhExpr !exit !ets = runEdhTx ets $
  evalExprSrc lhExpr $ \ !lhVal ->
    evalExprSrc rhExpr $
      \ !rhVal _ets -> case edhUltimate rhVal of
        EdhRange !lb !ub -> do
          let rhCmp = edhCompareValue ets lhVal (edhBoundValue ub) $ \case
                Nothing -> exitEdh ets exit edhNA
                Just LT -> exitEdh ets exit $ EdhBool $ inverse True
                Just GT -> exitEdh ets exit $ EdhBool $ inverse False
                Just EQ -> case ub of
                  OpenBound {} -> exitEdh ets exit $ EdhBool $ inverse False
                  ClosedBound {} -> exitEdh ets exit $ EdhBool $ inverse True
          edhCompareValue ets lhVal (edhBoundValue lb) $ \case
            Nothing -> exitEdh ets exit edhNA
            Just GT -> rhCmp
            Just LT -> exitEdh ets exit $ EdhBool $ inverse False
            Just EQ -> case lb of
              OpenBound {} -> exitEdh ets exit $ EdhBool $ inverse False
              ClosedBound {} -> rhCmp
        EdhList (List _u !lv) -> readTVar lv >>= chkInList lhVal
        EdhArgsPack (ArgsPack !vs !kwargs)
          | odNull kwargs ->
            chkInList lhVal vs
        _ -> edhValueDesc ets rhVal $ \ !badDesc ->
          throwEdh ets UsageError $ "bad range/container: " <> badDesc
  where
    chkInList :: EdhValue -> [EdhValue] -> STM ()
    chkInList !v !vs = exitEdh ets exit $ EdhBool $ inverse $ v `elem` vs

-- * identity equality tests

-- | operator (is)
idEqProc :: (Bool -> Bool) -> EdhIntrinsicOp
idEqProc inverse !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $
    \ !rhVal !ets ->
      (EdhBool . inverse <$> edhIdentEqual lhVal rhVal) >>= exitEdh ets exit

-- * ordering comparisons

-- | operator (>)
isGtProc :: EdhIntrinsicOp
isGtProc = edhOrdCmpOp $ \case
  GT -> True
  _ -> False

-- | operator (>=)
isGeProc :: EdhIntrinsicOp
isGeProc = edhOrdCmpOp $ \case
  GT -> True
  EQ -> True
  _ -> False

-- | operator (<)
isLtProc :: EdhIntrinsicOp
isLtProc = edhOrdCmpOp $ \case
  LT -> True
  _ -> False

-- | operator (<=)
isLeProc :: EdhIntrinsicOp
isLeProc = edhOrdCmpOp $ \case
  LT -> True
  EQ -> True
  _ -> False

edhOrdCmpOp :: (Ordering -> Bool) -> EdhIntrinsicOp
edhOrdCmpOp !cm !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case rhExpr of
    ExprSrc
      (InfixExpr rhSym@(opSym, _) midExpr@(ExprSrc _ mid'span) !rhExpr')
      _
        | opSym `elem` [">", ">=", "<", "<="] ->
          evalExprSrc midExpr $ \ !midVal !ets -> do
            -- chaining ordering comparisons
            edhCompareValue ets lhVal midVal $ \case
              Nothing ->
                edhValueDesc ets lhVal $
                  \ !lhDesc -> edhValueDesc ets midVal $ \ !midDesc ->
                    throwEdh ets EvalError $
                      "chained comparison ("
                        <> opSym
                        <> ") not applicable to "
                        <> lhDesc
                        <> " and "
                        <> midDesc
              Just !ord ->
                if cm ord
                  then
                    runEdhTx ets $
                      evalInfixSrc
                        rhSym
                        (ExprSrc (LitExpr (ValueLiteral midVal)) mid'span)
                        rhExpr'
                        exit
                  else -- short circuit
                    exitEdh ets exit $ EdhBool False
    _ -> evalExprSrc rhExpr $ \ !rhVal !ets ->
      edhCompareValue ets lhVal rhVal $ \case
        Nothing -> runEdhTx ets $ intrinsicOpReturnNA exit lhVal rhVal
        Just !ord -> exitEdh ets exit $ EdhBool $ cm ord
