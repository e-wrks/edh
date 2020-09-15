
module Language.Edh.Batteries.Vector where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Dynamic

import           Data.Vector.Mutable            ( IOVector )
import qualified Data.Vector                   as V
import qualified Data.Vector.Mutable           as MV

import qualified Data.Lossless.Decimal         as D

import           Language.Edh.Control
import           Language.Edh.InterOp
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.Evaluate

import           Language.Edh.Batteries.Math


-- Boxed Vector for Edh values, non-transactional, mutable anytime
type EdhVector = IOVector EdhValue


createVectorClass :: Scope -> STM Object
createVectorClass !clsOuterScope =
  mkHostClass' clsOuterScope "Vector" vecAllocator [] $ \ !clsScope -> do
    !mths <- sequence
      [ (AttrByName nm, ) <$> mkHostProc clsScope vc nm hp
      | (nm, vc, hp) <-
        [ ("append", EdhMethod, wrapHostProc vecAppendProc)
        , ("=="    , EdhMethod, wrapHostProc $ vecEqProc id)
        , ( "!="
          , EdhMethod
          , wrapHostProc $ vecEqProc not
          )
-- TODO support vectorized comparitions
        , ("[]"   , EdhMethod, wrapHostProc vecIdxReadProc)
        , ("[=]"  , EdhMethod, wrapHostProc vecIdxWriteProc)
        , ("[+=]" , EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc addProc)
        , ("[-=]" , EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc subtProc)
        , ("[*=]" , EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc mulProc)
        , ("[/=]" , EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc divProc)
        , ("[//=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc divIntProc)
        , ("[%=]" , EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc modIntProc)
        , ("[**=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc powProc)
        , ( "[&&=]"
          , EdhMethod
          , wrapHostProc $ vecIdxAssignWithOpProc logicalAndProc
          )
        , ( "[||=]"
          , EdhMethod
          , wrapHostProc $ vecIdxAssignWithOpProc logicalOrProc
          )
        , ("+"       , EdhMethod, wrapHostProc $ vecCopyWithOpProc addProc)
        , ("-"       , EdhMethod, wrapHostProc $ vecCopyWithOpProc subtProc)
        , ("*"       , EdhMethod, wrapHostProc $ vecCopyWithOpProc mulProc)
        , ("/"       , EdhMethod, wrapHostProc $ vecCopyWithOpProc divProc)
        , ("//"      , EdhMethod, wrapHostProc $ vecCopyWithOpProc divIntProc)
        , ("%"       , EdhMethod, wrapHostProc $ vecCopyWithOpProc modIntProc)
        , ("**"      , EdhMethod, wrapHostProc $ vecCopyWithOpProc powProc)
        , ("&&", EdhMethod, wrapHostProc $ vecCopyWithOpProc logicalAndProc)
        , ("||", EdhMethod, wrapHostProc $ vecCopyWithOpProc logicalOrProc)
        , ("+="      , EdhMethod, wrapHostProc $ vecAssignWithOpProc addProc)
        , ("-="      , EdhMethod, wrapHostProc $ vecAssignWithOpProc subtProc)
        , ("*="      , EdhMethod, wrapHostProc $ vecAssignWithOpProc mulProc)
        , ("/="      , EdhMethod, wrapHostProc $ vecAssignWithOpProc divProc)
        , ("//="     , EdhMethod, wrapHostProc $ vecAssignWithOpProc divIntProc)
        , ("%="      , EdhMethod, wrapHostProc $ vecAssignWithOpProc modIntProc)
        , ("**="     , EdhMethod, wrapHostProc $ vecAssignWithOpProc powProc)
        , ("&&=", EdhMethod, wrapHostProc $ vecAssignWithOpProc logicalAndProc)
        , ("||=", EdhMethod, wrapHostProc $ vecAssignWithOpProc logicalOrProc)
        , ("__null__", EdhMethod, wrapHostProc vecNullProc)
        , ("__len__" , EdhMethod, wrapHostProc vecLenProc)
        , ("__repr__", EdhMethod, wrapHostProc vecReprProc)
        ]
      ]
    iopdUpdate mths $ edh'scope'entity clsScope

 where

  -- | host constructor Vector(*elements,length=None)
  vecAllocator :: EdhObjectAllocator
  vecAllocator !etsCtor (ArgsPack !ctorArgs !ctorKwargs) !ctorExit = do
    let doIt :: Int -> [EdhValue] -> STM ()
        -- note @vs@ got to be lazy
        doIt !len vs = do
          let !vec = case len of
                _ | len < 0 -> V.fromList vs
                _           -> V.fromListN len vs
          !mvec <- unsafeIOToSTM $ V.thaw vec
          !hsv  <- newTVar $ toDyn mvec
          ctorExit $ HostStore hsv
    case odLookup (AttrByName "length") ctorKwargs of
      Nothing              -> doIt (-1) ctorArgs
      Just (EdhDecimal !d) -> case D.decimalToInteger d of
        Just !len | len >= 0 ->
          doIt (fromInteger len) $ ctorArgs ++ repeat edhNA
        _ ->
          throwEdh etsCtor UsageError
            $  "length not an positive integer: "
            <> T.pack (show d)
      Just !badLenVal ->
        throwEdh etsCtor UsageError $ "invalid length: " <> T.pack
          (show badLenVal)

  vecAppendProc :: [EdhValue] -> EdhHostProc
  vecAppendProc !args !exit !ets =
    withThisHostObj ets $ \ !hsv (mvec :: EdhVector) -> do
      !mvec' <-
        unsafeIOToSTM $ V.thaw =<< (V.++ V.fromList args) <$> V.freeze mvec
      writeTVar hsv $ toDyn mvec'
      exitEdh ets exit $ EdhObject $ edh'scope'this $ contextScope $ edh'context
        ets

  vecEqProc :: (Bool -> Bool) -> EdhValue -> EdhHostProc
  vecEqProc !inversion !other !exit !ets = case other of
    EdhObject !objOther -> withThisHostObj ets $ \_ (mvec :: EdhVector) ->
      withHostObject' objOther naExit $ \_ !mvecOther -> do
        !conclusion <- unsafeIOToSTM $ do
          -- TODO we're sacrificing thread safety for zero-copy performance
          --      here, justify this decision
          !vec      <- V.unsafeFreeze mvec
          !vecOther <- V.unsafeFreeze mvecOther
          return $ vec == vecOther
        exitEdh ets exit $ EdhBool $ inversion conclusion
    _ -> naExit
    where naExit = exitEdh ets exit $ EdhBool $ inversion False

  vecIdxReadProc :: EdhValue -> EdhHostProc
  vecIdxReadProc !idxVal !exit !ets =
    withHostObject ets thisVecObj $ \_ !mvec -> do
      let exitWith :: EdhVector -> STM ()
          exitWith !newVec = do
            !newStore <- HostStore <$> newTVar (toDyn newVec)
            edhMutCloneObj ets thisVecObj (edh'scope'that scope) newStore
              $ \ !thatObjClone -> exitEdh ets exit $ EdhObject thatObjClone
          exitWithRange :: Int -> Int -> Int -> STM ()
          exitWithRange !start !stop !step = do
            !newVec <- unsafeIOToSTM $ do
              let (q, r) = quotRem (stop - start) step
                  !len   = if r == 0 then abs q else 1 + abs q
              !newVec <- MV.new len
              let cpElems :: Int -> Int -> IO ()
                  cpElems !n !i = if i >= len
                    then return ()
                    else do
                      MV.unsafeRead mvec n >>= MV.unsafeWrite newVec i
                      cpElems (n + step) (i + 1)
              cpElems start 0
              return newVec
            exitWith newVec

      parseEdhIndex ets idxVal $ \case
        Left !err -> throwEdh ets UsageError err
        Right (EdhIndex !i) ->
          unsafeIOToSTM (MV.read mvec i) >>= exitEdh ets exit
        Right EdhAny -> exitEdh ets exit $ EdhObject thisVecObj
        Right EdhAll -> exitEdh ets exit $ EdhObject thisVecObj
        Right (EdhSlice !start !stop !step) ->
          edhRegulateSlice ets (MV.length mvec) (start, stop, step)
            $ \(!iStart, !iStop, !iStep) -> if iStep == 1
                then exitWith $ MV.unsafeSlice iStart (iStop - iStart) mvec
                else exitWithRange iStart iStop iStep
   where
    !scope      = contextScope $ edh'context ets
    !thisVecObj = edh'scope'this scope

  vecIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
  vecIdxWriteProc !idxVal !other !exit !ets =
    withThisHostObj ets $ \_ !mvec -> do
      let exitWithRangeAssign :: Int -> Int -> Int -> STM ()
          exitWithRangeAssign !start !stop !step = case edhUltimate other of
            EdhObject !objOther ->
              withHostObject' objOther exitWithNonVecAssign $ \_ !mvecOther ->
                do
                  unsafeIOToSTM $ assignWithVec start 0 mvecOther
                  exitEdh ets exit other
            _ -> exitWithNonVecAssign
           where
            (q, r)               = quotRem (stop - start) step
            !len                 = if r == 0 then abs q else 1 + abs q
            exitWithNonVecAssign = case edhUltimate other of
              EdhArgsPack (ArgsPack !args' _) -> do
                unsafeIOToSTM $ assignWithList start $ take len args'
                exitEdh ets exit other
              EdhList (List _ !lsv) -> do
                !ls <- readTVar lsv
                unsafeIOToSTM $ assignWithList start $ take len ls
                exitEdh ets exit other
              !badList ->
                throwEdh ets UsageError
                  $  "not assignable to indexed vector: "
                  <> T.pack (edhTypeNameOf badList)
            assignWithList :: Int -> [EdhValue] -> IO ()
            assignWithList _  []       = return ()
            assignWithList !n (x : xs) = do
              MV.unsafeWrite mvec n x
              assignWithList (n + step) xs
            assignWithVec :: Int -> Int -> EdhVector -> IO ()
            assignWithVec !n !i !mvec' = if i >= len || i >= MV.length mvec'
              then return ()
              else do
                MV.unsafeRead mvec' i >>= MV.unsafeWrite mvec n
                assignWithVec (n + step) (i + 1) mvec'

      parseEdhIndex ets idxVal $ \case
        Left  !err          -> throwEdh ets UsageError err
        Right (EdhIndex !i) -> do
          unsafeIOToSTM $ MV.unsafeWrite mvec i other
          exitEdh ets exit other
        Right EdhAny -> do
          unsafeIOToSTM $ MV.set mvec other
          exitEdh ets exit other
        Right EdhAll -> exitWithRangeAssign 0 (MV.length mvec) 1
        Right (EdhSlice !start !stop !step) ->
          edhRegulateSlice ets (MV.length mvec) (start, stop, step)
            $ \(!iStart, !iStop, !iStep) ->
                exitWithRangeAssign iStart iStop iStep

  vecCopyWithOpProc :: EdhIntrinsicOp -> EdhValue -> EdhHostProc
  vecCopyWithOpProc !withOp !other !exit !ets =
    withHostObject ets thisVecObj $ \_ !mvec ->
      unsafeIOToSTM (MV.new $ MV.length mvec) >>= \ !newVec ->
        let
          copyAt :: Int -> STM ()
          copyAt !n = if n < 0
            then do
              !newStore <- HostStore <$> newTVar (toDyn newVec)
              edhMutCloneObj ets thisVecObj (edh'scope'that scope) newStore
                $ \ !thatObjClone -> exitEdh ets exit $ EdhObject thatObjClone
            else unsafeIOToSTM (MV.read mvec n) >>= \ !srcVal ->
              runEdhTx ets
                $ withOp (LitExpr $ ValueLiteral srcVal)
                         (LitExpr $ ValueLiteral other)
                $ \ !opRtnV _ets -> do
                    unsafeIOToSTM $ MV.unsafeWrite newVec n opRtnV
                    copyAt (n - 1)
        in
          copyAt (MV.length mvec - 1)
   where
    !scope      = contextScope $ edh'context ets
    !thisVecObj = edh'scope'this scope


  opAssignElems
    :: EdhThreadState
    -> EdhIntrinsicOp
    -> EdhValue
    -> EdhVector
    -> Int
    -> Int
    -> Int
    -> STM ()
    -> STM ()
  opAssignElems !ets !withOp !rhVal !mvec !start !stop !step !exit = assignAt
    start
   where
    assignAt :: Int -> STM ()
    assignAt !n = if n >= stop
      then exit
      else unsafeIOToSTM (MV.read mvec n) >>= \ !oldVal ->
        runEdhTx ets
          $ withOp (LitExpr $ ValueLiteral oldVal)
                   (LitExpr $ ValueLiteral rhVal)
          $ \ !opRtnV _ets -> do
              unsafeIOToSTM $ MV.unsafeWrite mvec n opRtnV
              assignAt (n + step)

  vecAssignWithOpProc :: EdhIntrinsicOp -> EdhValue -> EdhHostProc
  vecAssignWithOpProc !withOp !other !exit !ets =
    withHostObject ets thisVecObj $ \_ !mvec ->
      opAssignElems ets withOp other mvec 0 (MV.length mvec) 1
        $ exitEdh ets exit
        $ EdhObject thisVecObj
   where
    !scope      = contextScope $ edh'context ets
    !thisVecObj = edh'scope'this scope

  opAssignRange
    :: EdhThreadState
    -> EdhIntrinsicOp
    -> EdhValue
    -> EdhVector
    -> Int
    -> Int
    -> Int
    -> EdhTxExit
    -> STM ()
  opAssignRange !ets !withOp !rhVal !mvec !start !stop !step !exit =
    case edhUltimate rhVal of
      EdhObject !objOther -> withHostObject' objOther exitWithNonVecAssign
        $ \_ !mvecOther -> assignWithVec start 0 mvecOther
      _ -> exitWithNonVecAssign
   where
    (q, r)               = quotRem (stop - start) step
    !len                 = if r == 0 then abs q else 1 + abs q
    exitWithNonVecAssign = case edhUltimate rhVal of
      EdhArgsPack (ArgsPack !args' _) -> assignWithList start $ take len args'
      EdhList (List _ !lsv) -> do
        !ls <- readTVar lsv
        assignWithList start $ take len ls
      _ -> opAssignElems ets withOp rhVal mvec start stop step
        $ exitEdh ets exit nil
    assignWithList :: Int -> [EdhValue] -> STM ()
    assignWithList _ [] = exitEdh ets exit nil
    assignWithList !n (x : xs) =
      unsafeIOToSTM (MV.read mvec n) >>= \ !oldVal ->
        runEdhTx ets
          $ withOp (LitExpr $ ValueLiteral oldVal) (LitExpr $ ValueLiteral x)
          $ \ !opRtnV _ets -> do
              unsafeIOToSTM $ MV.unsafeWrite mvec n opRtnV
              assignWithList (n + step) xs
    assignWithVec :: Int -> Int -> EdhVector -> STM ()
    assignWithVec !n !i !mvec' = if i >= len || i >= MV.length mvec'
      then exitEdh ets exit nil
      else do
        !oldVal   <- unsafeIOToSTM $ MV.unsafeRead mvec n
        !otherVal <- unsafeIOToSTM $ MV.unsafeRead mvec' i
        runEdhTx ets
          $ withOp (LitExpr $ ValueLiteral oldVal)
                   (LitExpr $ ValueLiteral otherVal)
          $ \ !opRtnV _ets -> do
              unsafeIOToSTM $ MV.unsafeWrite mvec n opRtnV
              assignWithVec (n + step) (i + 1) mvec'

  vecIdxAssignWithOpProc
    :: EdhIntrinsicOp -> EdhValue -> EdhValue -> EdhHostProc
  vecIdxAssignWithOpProc !withOp !idxVal !other !exit !ets =
    withThisHostObj ets $ \_ !mvec -> parseEdhIndex ets idxVal $ \case
      Left  !err          -> throwEdh ets UsageError err
      Right (EdhIndex !i) -> unsafeIOToSTM (MV.read mvec i) >>= \ !oldVal ->
        runEdhTx ets
          $ withOp (LitExpr $ ValueLiteral oldVal)
                   (LitExpr $ ValueLiteral other)
          $ \ !opRtnV _ets -> do
              unsafeIOToSTM $ MV.unsafeWrite mvec i opRtnV
              exitEdh ets exit opRtnV
      Right EdhAny ->
        opAssignElems ets withOp other mvec 0 (MV.length mvec) 1
          $ exitEdh ets exit nil
      Right EdhAll ->
        opAssignRange ets withOp other mvec 0 (MV.length mvec) 1 exit
      Right (EdhSlice !start !stop !step) ->
        edhRegulateSlice ets (MV.length mvec) (start, stop, step)
          $ \(!iStart, !iStop, !iStep) ->
              opAssignRange ets withOp other mvec iStart iStop iStep exit


  vecNullProc :: EdhHostProc
  vecNullProc !exit !ets = withThisHostObj ets $ \_ (mvec :: EdhVector) ->
    exitEdh ets exit $ EdhBool $ MV.length mvec <= 0

  vecLenProc :: EdhHostProc
  vecLenProc !exit !ets = withThisHostObj ets $ \_ (mvec :: EdhVector) ->
    exitEdh ets exit $ EdhDecimal $ fromIntegral $ MV.length mvec

  vecReprProc :: EdhHostProc
  vecReprProc !exit !ets = withThisHostObj ets $ \_ (mvec :: EdhVector) -> do
    let go :: [EdhValue] -> [Text] -> STM ()
        go [] !rs =
          exitEdh ets exit
            $  EdhString
            $  "Vector("
            <> T.intercalate "," (reverse rs)
            <> ")"
        go (v : rest) rs = edhValueRepr ets v $ \ !r -> go rest (r : rs)
    !vec <- unsafeIOToSTM $ V.freeze mvec
    go (V.toList vec) []

