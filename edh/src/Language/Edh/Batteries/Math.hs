
module Language.Edh.Batteries.Math where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.Reader
import           Control.Concurrent.STM

import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

import           Data.Lossless.Decimal

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | operator (+)
addProc :: EdhIntrinsicOp
addProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal rhNum -> exitEdhProc exit (EdhDecimal $ lhNum + rhNum)
        _ ->
          throwEdh EvalError
            $  "Invalid right-hand value for (+) operation: "
            <> T.pack (show rhVal)
    EdhString lhs -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      edhValueStr rhVal $ \(OriginalValue rhStr _ _) -> case rhStr of
        EdhString !rhs -> exitEdhProc exit (EdhString $ lhs <> rhs)
        _              -> error "bug: edhValueStr returned non-string"
    _ ->
      throwEdh EvalError
        $  "Invalid left-hand value for (+) operation: "
        <> T.pack (show lhVal)


-- | operator (-)
subsProc :: EdhIntrinsicOp
subsProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal rhNum -> exitEdhProc exit (EdhDecimal $ lhNum - rhNum)
        _ ->
          throwEdh EvalError
            $  "Invalid right-hand value for (-) operation: "
            <> T.pack (show rhVal)
    _ ->
      throwEdh EvalError
        $  "Invalid left-hand value for (-) operation: "
        <> T.pack (show lhVal)


-- | operator (*)
mulProc :: EdhIntrinsicOp
mulProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal rhNum -> exitEdhProc exit (EdhDecimal $ lhNum * rhNum)
        _ ->
          throwEdh EvalError
            $  "Invalid right-hand value for (*) operation: "
            <> T.pack (show rhVal)
    _ ->
      throwEdh EvalError
        $  "Invalid left-hand value for (*) operation: "
        <> T.pack (show lhVal)


-- | operator (/)
divProc :: EdhIntrinsicOp
divProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal rhNum -> exitEdhProc exit (EdhDecimal $ lhNum / rhNum)
        _ ->
          throwEdh EvalError
            $  "Invalid right-hand value for (/) operation: "
            <> T.pack (show rhVal)
    _ ->
      throwEdh EvalError
        $  "Invalid left-hand value for (/) operation: "
        <> T.pack (show lhVal)

-- | operator (//) integer division, following Python 
-- http://python-history.blogspot.com/2010/08/why-pythons-integer-division-floors.html
divIntProc :: EdhIntrinsicOp
divIntProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal lhNum -> case decimalToInteger lhNum of
      Nothing ->
        throwEdh EvalError
          $  "Not an integer as left-hand value for (//) operation: "
          <> T.pack (show lhNum)
      Just lhi -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
        case edhUltimate rhVal of
          EdhDecimal rhNum -> case decimalToInteger rhNum of
            Nothing ->
              throwEdh EvalError
                $  "Not an integer as right-hand value for (//) operation: "
                <> T.pack (show rhNum)
            Just rhi ->
              exitEdhProc exit $ EdhDecimal $ Decimal 1 0 $ lhi `div` rhi
          _ ->
            throwEdh EvalError
              $  "Invalid right-hand value for (//) operation: "
              <> T.pack (show rhVal)
    _ ->
      throwEdh EvalError
        $  "Invalid left-hand value for (//) operation: "
        <> T.pack (show lhVal)

-- | operator (%) modulus of integer division, following Python 
-- http://python-history.blogspot.com/2010/08/why-pythons-integer-division-floors.html
modIntProc :: EdhIntrinsicOp
modIntProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal lhNum -> case decimalToInteger lhNum of
      Nothing ->
        throwEdh EvalError
          $  "Not an integer as left-hand value for (%) operation: "
          <> T.pack (show lhNum)
      Just lhi -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
        case edhUltimate rhVal of
          EdhDecimal rhNum -> case decimalToInteger rhNum of
            Nothing ->
              throwEdh EvalError
                $  "Not an integer as right-hand value for (%) operation: "
                <> T.pack (show rhNum)
            Just rhi ->
              exitEdhProc exit $ EdhDecimal $ Decimal 1 0 $ lhi `mod` rhi
          _ ->
            throwEdh EvalError
              $  "Invalid right-hand value for (%) operation: "
              <> T.pack (show rhVal)
    _ ->
      throwEdh EvalError
        $  "Invalid left-hand value for (%) operation: "
        <> T.pack (show lhVal)


-- | operator (**)
powProc :: EdhIntrinsicOp
powProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhDecimal lhNum -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhDecimal (Decimal rh'd rh'e rh'n) -> if rh'd /= 1
          then
            throwEdh EvalError
            $  "Invalid right-hand value for (**) operation: "
            <> T.pack (show rhVal)
          else exitEdhProc exit (EdhDecimal $ lhNum ^^ (rh'n * 10 ^ rh'e))
        _ ->
          throwEdh EvalError
            $  "Invalid right-hand value for (**) operation: "
            <> T.pack (show rhVal)
    _ ->
      throwEdh EvalError
        $  "Invalid left-hand value for (**) operation: "
        <> T.pack (show lhVal)


-- | operator (&&)
logicalAndProc :: EdhIntrinsicOp
logicalAndProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhBool lhBool -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhBool rhBool -> exitEdhProc exit (EdhBool $ lhBool && rhBool)
        _ -> throwEdh EvalError $ "Invalid right-hand value type: " <> T.pack
          (edhTypeNameOf rhVal)
    _ -> throwEdh EvalError $ "Invalid left-hand value type: " <> T.pack
      (edhTypeNameOf lhVal)

-- | operator (||)
logicalOrProc :: EdhIntrinsicOp
logicalOrProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhBool lhBool -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      case edhUltimate rhVal of
        EdhBool rhBool -> exitEdhProc exit (EdhBool $ lhBool || rhBool)
        _ -> throwEdh EvalError $ "Invalid right-hand value type: " <> T.pack
          (edhTypeNameOf rhVal)
    _ -> throwEdh EvalError $ "Invalid left-hand value type: " <> T.pack
      (edhTypeNameOf lhVal)


-- | operator (~=)
valEqProc :: EdhIntrinsicOp
valEqProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  let
    cmp2List :: [EdhValue] -> [EdhValue] -> STM Bool
    cmp2List []               []               = return True
    cmp2List (_ : _)          []               = return False
    cmp2List []               (_     : _     ) = return False
    cmp2List (lhVal : lhRest) (rhVal : rhRest) = cmp2Val lhVal rhVal >>= \case
      False -> return False
      True  -> cmp2List lhRest rhRest
    cmp2Map :: [(ItemKey, EdhValue)] -> [(ItemKey, EdhValue)] -> STM Bool
    cmp2Map []      []      = return True
    cmp2Map (_ : _) []      = return False
    cmp2Map []      (_ : _) = return False
    cmp2Map ((lhKey, lhVal) : lhRest) ((rhKey, rhVal) : rhRest) =
      if lhKey /= rhKey
        then return False
        else cmp2Val lhVal rhVal >>= \case
          False -> return False
          True  -> cmp2Map lhRest rhRest
    cmp2Val :: EdhValue -> EdhValue -> STM Bool
    cmp2Val lhVal rhVal = if lhVal == rhVal
      then return True
      else case edhUltimate lhVal of
        EdhList (List _ lhll) -> case edhUltimate rhVal of
          EdhList (List _ rhll) -> do
            lhl <- readTVar lhll
            rhl <- readTVar rhll
            cmp2List lhl rhl
          _ -> return False
        EdhDict (Dict _ lhd) -> case edhUltimate rhVal of
          EdhDict (Dict _ rhd) -> do
            lhm <- readTVar lhd
            rhm <- readTVar rhd
            cmp2Map (Map.toList lhm) (Map.toList rhm)
          _ -> return False
        _ -> return False
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> if lhVal == rhVal
      then exitEdhProc exit true
      else contEdhSTM $ cmp2Val lhVal rhVal >>= \conclusion ->
        exitEdhSTM pgs exit (EdhBool conclusion)


-- | operator (==)
idEqProc :: EdhIntrinsicOp
idEqProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      exitEdhProc exit (EdhBool $ lhVal == rhVal)

-- | operator (!=)
idNeProc :: EdhIntrinsicOp
idNeProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      exitEdhProc exit (EdhBool $ lhVal /= rhVal)


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
  Nothing ->
    throwEdhSTM pgs EvalError
      $  "Not comparable: "
      <> T.pack (edhTypeNameOf lhVal)
      <> " vs "
      <> T.pack (edhTypeNameOf rhVal)
  Just ord -> exitEdhSTM pgs exit (EdhBool $ cm ord)

compareEdhValue :: EdhValue -> EdhValue -> STM (Maybe Ordering)
compareEdhValue lhVal rhVal = case edhUltimate lhVal of
  EdhDecimal lhNum -> case edhUltimate rhVal of
    EdhDecimal rhNum -> return $ Just $ compare lhNum rhNum
    _                -> return Nothing
  EdhString lhStr -> case edhUltimate rhVal of
    EdhString rhStr -> return $ Just $ compare lhStr rhStr
    _               -> return Nothing
  EdhBool lhCnd -> case edhUltimate rhVal of
    EdhBool rhCnd -> return $ Just $ compare lhCnd rhCnd
    _             -> return Nothing
  _ -> return Nothing

