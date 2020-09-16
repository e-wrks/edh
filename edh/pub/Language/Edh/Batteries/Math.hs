
module Language.Edh.Batteries.Math where

import           Prelude
-- import           Debug.Trace

import           Control.Concurrent.STM

import qualified Data.Text                     as T
import qualified Data.Text.Encoding            as TE
import           Data.Maybe

import           Data.Lossless.Decimal

import           Language.Edh.Control
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.CoreLang
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
          $  "should not (+) a "
          <> T.pack (edhTypeNameOf rhVal)
          <> " to a blob."
    EdhString !lhs -> evalExpr rhExpr $ \ !rhv !ets ->
      edhValueStr ets (edhUltimate rhv)
        $ \ !rhs -> exitEdh ets exit (EdhString $ lhs <> rhs)
    _ -> exitEdhTx exit edhNA


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

doEdhComparison
  :: EdhThreadState
  -> EdhValue
  -> EdhValue
  -> (Maybe Ordering -> STM ())
  -> STM ()
doEdhComparison !ets !lhVal !rhVal !exit = case edhUltimate lhVal of
  EdhObject !lhObj -> case edh'obj'store lhObj of
    ClassStore{} ->
      lookupEdhObjAttr (edh'obj'class lhObj) cmpMagicKey
        >>= tryMagic id lhObj rhVal tryRightHandMagic
    _ ->
      lookupEdhObjAttr lhObj cmpMagicKey
        >>= tryMagic id lhObj rhVal tryRightHandMagic
  _ -> tryRightHandMagic
 where
  cmpMagicKey = AttrByName "__compare__"

  inverse :: Ordering -> Ordering
  inverse = \case
    EQ -> EQ
    LT -> GT
    GT -> LT

  tryRightHandMagic = case edhUltimate rhVal of
    EdhObject !rhObj -> case edh'obj'store rhObj of
      ClassStore{} ->
        lookupEdhObjAttr (edh'obj'class rhObj) cmpMagicKey
          >>= tryMagic inverse rhObj lhVal noMagic
      _ ->
        lookupEdhObjAttr rhObj cmpMagicKey
          >>= tryMagic inverse rhObj lhVal noMagic
    _ -> noMagic

  tryMagic
    :: (Ordering -> Ordering)
    -> Object
    -> EdhValue
    -> STM ()
    -> (Object, EdhValue)
    -> STM ()
  tryMagic !reorder !obj !opponent !naExit = \case
    (_     , EdhNil                         ) -> naExit
    (!this', EdhProcedure (EdhMethod !mth) _) -> runEdhTx ets $ callEdhMethod
      this'
      obj
      mth
      (ArgsPack [opponent] odEmpty)
      id
      chkMagicRtn
    (_, EdhBoundProc (EdhMethod !mth) !this !that _) ->
      runEdhTx ets $ callEdhMethod this
                                   that
                                   mth
                                   (ArgsPack [opponent] odEmpty)
                                   id
                                   chkMagicRtn
    (_, !badCmpMagic) -> edhValueDesc ets badCmpMagic $ \ !badDesc ->
      throwEdh ets UsageError $ "bad __compare__ magic: " <> badDesc
   where
    chkMagicRtn :: EdhTxExit
    chkMagicRtn !magicRtn _ets = case edhUltimate magicRtn of
      EdhDefault _ !exprDef !etsDef ->
        runEdhTx (fromMaybe ets etsDef)
          $ evalExpr (deExpr exprDef)
          $ \ !defVal _ets -> chkMagicExit defVal
      _ -> chkMagicExit magicRtn
     where
      chkMagicExit :: EdhValue -> STM ()
      chkMagicExit = \case
        EdhNil      -> naExit
        EdhOrd !ord -> exit $ Just $ reorder ord
        _           -> edhValueDesc ets magicRtn $ \ !badDesc ->
          throwEdh ets UsageError
            $  "invalid result from __compare__: "
            <> badDesc

  noMagic :: STM ()
  noMagic = case edhUltimate lhVal of
    EdhDecimal !lhNum -> case edhUltimate rhVal of
      EdhDecimal !rhNum -> exit $ Just $ compare lhNum rhNum
      _                 -> exit Nothing
    EdhString lhStr -> case edhUltimate rhVal of
      EdhString rhStr -> exit $ Just $ compare lhStr rhStr
      _               -> exit Nothing
    EdhBool lhCnd -> case edhUltimate rhVal of
      EdhBool rhCnd -> exit $ Just $ compare lhCnd rhCnd
      _             -> exit Nothing
    _ -> exit Nothing

