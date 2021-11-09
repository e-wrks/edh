module Language.Edh.Batteries.Math where

-- import           Debug.Trace

import Control.Concurrent.STM
import Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import Language.Edh.Args
import Language.Edh.Batteries.Data
import Language.Edh.Batteries.InterOp
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
        EdhDecimal !rhNum -> exitEdhTx exit $ EdhDecimal $ lhNum + rhNum
        EdhQty (Quantity rhq rhu) ->
          unifyToUnit
            rhu
            (Left lhNum)
            (\lhq -> exitEdhTx exit $ EdhQty $ Quantity (lhq + rhq) rhu)
            (exitEdhTx exit $ EdhQty $ Quantity (lhNum + rhq) rhu)
        _ ->
          concatProc
            (ExprSrc (LitExpr (ValueLiteral lhVal)) noSrcRange)
            (ExprSrc (LitExpr (ValueLiteral rhVal)) noSrcRange)
            exit
    EdhQty lhQty@(Quantity lhq lhu) -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum ->
          unifyToUnit
            lhu
            (Left rhNum)
            (\rhq -> exitEdhTx exit $ EdhQty $ Quantity (lhq + rhq) lhu)
            (exitEdhTx exit $ EdhQty $ Quantity (lhq + rhNum) lhu)
        EdhQty rhQty -> qtyAddSub (+) lhQty rhQty exit
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

qtyAddSub ::
  (Decimal -> Decimal -> Decimal) ->
  Quantity ->
  Quantity ->
  EdhTxExit EdhValue ->
  EdhTx
qtyAddSub op lhQty0@(Quantity lhq0 lhu0) rhQty0@(Quantity rhq0 rhu0) exit =
  if lhu0 == rhu0
    then exitEdhTx exit $ EdhQty $ Quantity (lhq0 `op` rhq0) lhu0
    else
      unifyToPrimUnit
        lhQty0
        ( \lhuq ->
            unifyToPrimUnit
              rhQty0
              (tryPrimaryArith lhuq)
              (tryDirectConversion lhQty0 rhQty0)
        )
        (tryDirectConversion lhQty0 rhQty0)
  where
    tryPrimaryArith ::
      Either Decimal Quantity ->
      Either Decimal Quantity ->
      EdhTx
    tryPrimaryArith lhuq rhuq = case lhuq of
      Left lhNum -> case rhuq of
        Left rhNum -> exitEdhTx exit $ EdhDecimal $ lhNum `op` rhNum
        Right {} ->
          exitEdhTx exit $ EdhQty $ Quantity (lhNum `op` rhq0) rhu0
      Right lhQty'@(Quantity lhq' lhu') -> case rhuq of
        Left rhNum ->
          exitEdhTx exit $ EdhQty $ Quantity (lhq0 `op` rhNum) lhu0
        Right rhQty'@(Quantity rhq' rhu') ->
          if lhu' == rhu'
            then exitEdhTx exit $ EdhQty $ Quantity (lhq' `op` rhq') lhu'
            else tryDirectConversion lhQty' rhQty'

    tryDirectConversion :: Quantity -> Quantity -> EdhTx
    tryDirectConversion lhQty@(Quantity lhq lhu) rhQty@(Quantity rhq rhu) =
      unifyToUnit
        lhu
        (Right rhQty)
        ( \rhq' ->
            exitEdhTx exit $ EdhQty $ Quantity (lhq `op` rhq') lhu
        )
        ( unifyToUnit
            rhu
            (Right lhQty)
            ( \lhq' ->
                exitEdhTx exit $
                  EdhQty $ Quantity (lhq' `op` rhq) rhu
            )
            ( throwEdhTx UsageError $
                "can not unify the two units: ["
                  <> uomDefiIdent lhu
                  <> "] and ["
                  <> uomDefiIdent rhu
                  <> "]"
            )
        )

-- | operator (-)
subtProc :: EdhIntrinsicOp
subtProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum - rhNum)
        EdhQty (Quantity rhq rhu) ->
          unifyToUnit
            rhu
            (Left lhNum)
            (\lhq -> exitEdhTx exit $ EdhQty $ Quantity (lhq - rhq) rhu)
            (exitEdhTx exit $ EdhQty $ Quantity (lhNum - rhq) rhu)
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    EdhQty lhQty@(Quantity lhq lhu) -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum ->
          unifyToUnit
            lhu
            (Left rhNum)
            (\rhq -> exitEdhTx exit $ EdhQty $ Quantity (lhq - rhq) lhu)
            (exitEdhTx exit $ EdhQty $ Quantity (lhq - rhNum) lhu)
        EdhQty rhQty -> qtyAddSub (-) lhQty rhQty exit
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (*)
mulProc :: EdhIntrinsicOp
mulProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum * rhNum)
        EdhQty (Quantity rhq rhu) ->
          exitEdhTx exit $ EdhQty $ Quantity (lhNum * rhq) rhu
        EdhString !rhStr -> case D.decimalToInteger lhNum of
          Just lhInt ->
            exitEdhTx exit $ EdhString $ T.replicate (fromIntegral lhInt) rhStr
          Nothing -> intrinsicOpReturnNA exit lhVal rhVal
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    EdhQty lhQty@(Quantity lhq lhu) -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum ->
          exitEdhTx exit $ EdhQty $ Quantity (lhq * rhNum) lhu
        EdhQty rhQty@(Quantity rhq rhu) -> qtyToPureNumber rhQty $ \case
          Just rhNum -> exitEdhTx exit $ EdhQty $ Quantity (lhq * rhNum) lhu
          Nothing -> qtyToPureNumber lhQty $ \case
            Just lhNum -> exitEdhTx exit $ EdhQty $ Quantity (lhNum * rhq) rhu
            Nothing ->
              exitEdhTx exit $
                EdhQty $ Quantity (lhq * rhq) (uomMultiply lhu rhu)
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    EdhString lhStr -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> case D.decimalToInteger rhNum of
          Just rhInt ->
            exitEdhTx exit $ EdhString $ T.replicate (fromIntegral rhInt) lhStr
          Nothing -> intrinsicOpReturnNA exit lhVal rhVal
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (/)
divProc :: EdhIntrinsicOp
divProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum -> exitEdhTx exit (EdhDecimal $ lhNum / rhNum)
        EdhQty rhQty@(Quantity rhq rhu) -> qtyToPureNumber rhQty $ \case
          Just rhNum -> exitEdhTx exit $ EdhDecimal $ lhNum / rhNum
          Nothing ->
            exitEdhTx exit $
              EdhQty $ Quantity (lhNum / rhq) (uomReciprocal rhu)
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    EdhQty (Quantity lhq lhu) -> evalExprSrc rhExpr $ \ !rhVal ->
      case edhUltimate rhVal of
        EdhDecimal !rhNum ->
          exitEdhTx exit $ EdhQty $ Quantity (lhq / rhNum) lhu
        EdhQty rhQty@(Quantity rhq rhu) -> qtyToPureNumber rhQty $ \case
          Just rhNum -> exitEdhTx exit $ EdhQty $ Quantity (lhq / rhNum) lhu
          Nothing ->
            exitEdhTx exit $ EdhQty $ Quantity (lhq / rhq) (uomDivide lhu rhu)
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (quot) integer division truncated toward zero
quotIntProc :: EdhIntrinsicOp
quotIntProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing -> intrinsicOpReturnNA'WithLHV exit lhVal
      Just !lhi -> evalExprSrc rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing -> intrinsicOpReturnNA exit lhVal rhVal
          Just !rhi ->
            exitEdhTx exit $ EdhDecimal $ Decimal 1 0 $ lhi `quot` rhi
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (rem) integer remainder, following Haskell
remIntProc :: EdhIntrinsicOp
remIntProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing -> intrinsicOpReturnNA'WithLHV exit lhVal
      Just lhi -> evalExprSrc rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing -> intrinsicOpReturnNA exit lhVal rhVal
          Just rhi -> exitEdhTx exit $ EdhDecimal $ Decimal 1 0 $ lhi `rem` rhi
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (//) integer division truncated toward negative infinity,
-- following Python
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

-- | operator (mod) integer modulus, following Haskell
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

-- | operator (quotRem) simultaneous quot and rem, following Haskell
quotRemIntProc :: EdhIntrinsicOp
quotRemIntProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing -> intrinsicOpReturnNA'WithLHV exit lhVal
      Just lhi -> evalExprSrc rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing -> intrinsicOpReturnNA exit lhVal rhVal
          Just rhi ->
            let (q, r) = lhi `quotRem` rhi
             in exitEdhTx exit $
                  EdhArgsPack $
                    ArgsPack
                      [EdhDecimal $ Decimal 1 0 q, EdhDecimal $ Decimal 1 0 r]
                      odEmpty
        _ -> intrinsicOpReturnNA exit lhVal rhVal
    _ -> intrinsicOpReturnNA'WithLHV exit lhVal

-- | operator (divMod) simultaneous div and mod, following Haskell
divModIntProc :: EdhIntrinsicOp
divModIntProc !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  case edhUltimate lhVal of
    EdhDecimal !lhNum -> case decimalToInteger lhNum of
      Nothing -> intrinsicOpReturnNA'WithLHV exit lhVal
      Just lhi -> evalExprSrc rhExpr $ \ !rhVal -> case edhUltimate rhVal of
        EdhDecimal !rhNum -> case decimalToInteger rhNum of
          Nothing -> intrinsicOpReturnNA exit lhVal rhVal
          Just rhi ->
            let (q, m) = lhi `divMod` rhi
             in exitEdhTx exit $
                  EdhArgsPack $
                    ArgsPack
                      [EdhDecimal $ Decimal 1 0 q, EdhDecimal $ Decimal 1 0 m]
                      odEmpty
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

-- | virtual attribute Decimal.finite
--
-- test whether the decimal value is finite, i.e. not inf/-inf/nan
decFiniteProc :: Decimal -> EdhHostProc
decFiniteProc !d !exit =
  exitEdhTx exit $ EdhBool $ decimalIsFinite d

-- | virtual attribute Decimal.ceil
--
-- get the least integer not less than x
decCeilProc :: Decimal -> EdhHostProc
decCeilProc !d !exit =
  exitEdhTx exit $ EdhDecimal $ fromInteger $ ceiling d

-- | virtual attribute Decimal.floor
--
-- get the the greatest integer not greater than x
decFloorProc :: Decimal -> EdhHostProc
decFloorProc !d !exit =
  exitEdhTx exit $ EdhDecimal $ fromInteger $ floor d

-- | virtual attribute Decimal.trunc
--
-- truncate to integer toward zero
decTruncProc :: Decimal -> EdhHostProc
decTruncProc !d !exit =
  exitEdhTx exit $ EdhDecimal $ fromInteger $ truncate d

-- | virtual attribute Decimal.round
--
-- round to integer toward zero
decRoundProc :: Decimal -> EdhHostProc
decRoundProc !d !exit =
  exitEdhTx exit $ EdhDecimal $ fromInteger $ round d

-- | virtual attribute Decimal.int
--
-- integer part (toward zero) as string
decIntProc :: Decimal -> EdhHostProc
decIntProc !d !exit =
  exitEdhTx exit $ EdhString $ T.pack $ show (truncate d :: Integer)

-- | virtual attribute Decimal.toFixed()
--
-- resembles `Number.prototype.toFixed()` as in JavaScript
decToFixedProc :: Decimal -> EdhHostProc
decToFixedProc !d !exit !ets =
  mkHostProc'
    (contextScope $ edh'context ets)
    EdhMethod
    "toFixed"
    (decToFixed d EdhString)
    >>= exitEdh ets exit

decToFixed ::
  Decimal ->
  (Text -> EdhValue) ->
  "digs" ?: Decimal ->
  EdhTxExit EdhValue ->
  EdhTx
decToFixed d cnvt (defaultArg 0 -> nDigs) !exit =
  case D.decimalToInteger nDigs of
    Just digs
      -- Mozilla suggests 0 ~ 20, and "implementations may optionally support
      -- a larger range of values", we choose 0 ~ 200 here.
      | 0 <= digs && digs <= 200 -> do
        let (iDigs :: Int) = fromInteger digs
        if
            | not (decimalIsFinite d) ->
              exitEdhTx exit $ cnvt $ T.pack $ show d
            | iDigs <= 0 -> do
              let (i :: Integer) = round d
              exitEdhTx exit $ cnvt $ T.pack $ show i
            | otherwise -> do
              let (amp :: Integer) = 10 ^ iDigs
                  (q, r) = round (fromInteger amp * d) `quotRem` amp
                  fracPart = show r
                  padZeros = replicate (iDigs - length fracPart) '0'
              exitEdhTx exit $
                cnvt $ T.pack $ show q <> "." <> fracPart <> padZeros
    _ ->
      throwEdhTx UsageError $
        "invalid number of decimal digits: " <> T.pack (show nDigs)

-- | virtual attribute UoM.unify
--
-- convert a quantity to be in the specified unit of measure
uomUnifyProc :: UnitDefi -> EdhHostProc
uomUnifyProc !uom !exit !ets =
  mkHostProc' (contextScope $ edh'context ets) EdhMethod "unifyQty" unifyQty
    >>= exitEdh ets exit
  where
    unifyQty :: EdhValue -> EdhHostProc
    unifyQty val !exit' =
      mustUnifyToUnit uom val $ exit' . EdhDecimal

-- | virtual attribute Qty.unified
--
-- convert a specified quantity to be in a primary unit of measure if possible
qtyUnifiedProc :: Quantity -> EdhHostProc
qtyUnifiedProc !qty !exit =
  unifyToPrimUnit
    qty
    ( \case
        Left d -> exitEdhTx exit $ EdhDecimal d
        Right q -> exitEdhTx exit $ EdhQty q
    )
    -- todo: or return as is?
    $ throwEdhTx UsageError $
      T.pack $ "no primary unit for " <> show qty <> " to be unified to"

-- | virtual attribute Qty.reduced
--
-- try convert a specified quantity with the goal for the number to be within
-- `0.9 ~ 10` scale range
qtyReducedProc :: Quantity -> EdhHostProc
qtyReducedProc !qty !exit =
  reduceQtyNumber qty (exit . EdhQty) (exit $ EdhQty qty)

-- | virtual attribute Qty.toFixed()
--
-- resembles `Number.prototype.toFixed()` as in JavaScript
qtyToFixedProc :: Quantity -> EdhHostProc
qtyToFixedProc (Quantity q uom) !exit !ets =
  mkHostProc'
    (contextScope $ edh'context ets)
    EdhMethod
    "toFixed"
    (decToFixed q $ EdhString . (<> uomDefiIdent uom))
    >>= exitEdh ets exit

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
      (InfixExpr rhSym@(OpSymSrc opSym _) midExpr@(ExprSrc _ mid'span) !rhExpr')
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

-- * in range/container test

inRangeProc ::
  (Bool -> Bool) ->
  ( EdhThreadState ->
    EdhValue ->
    EdhValue ->
    (Maybe Bool -> STM ()) ->
    STM ()
  ) ->
  EdhIntrinsicOp
inRangeProc inverse eqTester !lhExpr !rhExpr !exit !ets = runEdhTx ets $
  evalExprSrc lhExpr $ \ !lhVal ->
    evalExprSrc rhExpr $
      \ !rhVal _ets -> do
        let badRHS = edhSimpleDesc ets rhVal $ \ !badDesc ->
              throwEdh ets UsageError $ "bad range/container: " <> badDesc
        case edhUltimate rhVal of
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
          EdhArgsPack (ArgsPack !vs !kwargs) ->
            if null vs
              then edhValueAsAttrKey'
                ets
                lhVal
                (exitEdh ets exit $ EdhBool $ inverse False)
                $ \ !lhKey -> case odLookup lhKey kwargs of
                  Nothing -> exitEdh ets exit $ EdhBool $ inverse False
                  Just {} -> exitEdh ets exit $ EdhBool $ inverse True
              else chkInList lhVal vs
          EdhList (List _u !lv) -> readTVar lv >>= chkInList lhVal
          EdhDict (Dict _ !ds) ->
            iopdLookup lhVal ds >>= \case
              Nothing -> exitEdh ets exit $ EdhBool $ inverse False
              Just {} -> exitEdh ets exit $ EdhBool $ inverse True
          !rhUltiVal -> parseEdhIndex ets rhUltiVal $ \case
            Left _err -> badRHS
            Right (EdhSlice (Just !start) (Just !stop) !maybeStep) ->
              case maybeStep of
                Nothing -> do
                  let rhCmp =
                        edhCompareValue
                          ets
                          lhVal
                          (EdhDecimal $ fromIntegral stop)
                          $ \case
                            Nothing -> exitEdh ets exit edhNA
                            Just LT ->
                              exitEdh ets exit $ EdhBool $ inverse True
                            _ -> exitEdh ets exit $ EdhBool $ inverse False
                  edhCompareValue ets lhVal (EdhDecimal $ fromIntegral start) $
                    \case
                      Nothing -> exitEdh ets exit edhNA
                      Just LT -> exitEdh ets exit $ EdhBool $ inverse False
                      _ -> rhCmp
                Just !step -> do
                  let inDiscreteRange :: Integer -> Integer -> Integer -> STM ()
                      inDiscreteRange !start' !stop' !step' =
                        case edhUltimate lhVal of
                          EdhDecimal !d -> case D.decimalToInteger d of
                            Just !i
                              | start' <= i && i < stop'
                                  && ((i - start') `mod` step') == 0 ->
                                exitEdh ets exit $ EdhBool $ inverse True
                            _ -> exitEdh ets exit $ EdhBool $ inverse False
                          _ -> exitEdh ets exit edhNA
                  if
                      | stop == start ->
                        exitEdh ets exit $ EdhBool $ inverse False
                      | stop > start && step > 0 ->
                        inDiscreteRange
                          (fromIntegral start)
                          (fromIntegral stop)
                          (fromIntegral step)
                      | stop < start && step < 0 ->
                        inDiscreteRange
                          (fromIntegral stop)
                          (fromIntegral start)
                          (fromIntegral $ - step)
                      | otherwise ->
                        exitEdh ets exit $ EdhBool $ inverse False
            _ -> badRHS
  where
    chkInList :: EdhValue -> [EdhValue] -> STM ()
    chkInList _ [] =
      exitEdh ets exit $ EdhBool $ inverse False
    chkInList !v (e : rest) = eqTester ets v e $ \case
      Just True -> exitEdh ets exit $ EdhBool $ inverse True
      _ -> chkInList v rest

-- * identity equality tests

-- | operator (is)
idEqProc :: (Bool -> Bool) -> EdhIntrinsicOp
idEqProc inverse !lhExpr !rhExpr !exit = evalExprSrc lhExpr $ \ !lhVal ->
  evalExprSrc rhExpr $ \ !rhVal !ets ->
    edhIdentEqual lhVal rhVal >>= exitEdh ets exit . EdhBool . inverse

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
      (InfixExpr rhSym@(OpSymSrc opSym _) midExpr@(ExprSrc _ mid'span) !rhExpr')
      _
        | opSym `elem` [">", ">=", "<", "<="] ->
          evalExprSrc midExpr $ \ !midVal !ets -> do
            -- chaining ordering comparisons
            edhCompareValue ets lhVal midVal $ \case
              Nothing ->
                edhSimpleDesc ets lhVal $
                  \ !lhDesc -> edhSimpleDesc ets midVal $ \ !midDesc ->
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
