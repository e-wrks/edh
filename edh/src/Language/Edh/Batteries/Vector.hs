
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
      [ (AttrByName nm, ) <$> mkHostProc clsScope vc nm hp mthArgs
      | (nm, vc, hp, mthArgs) <-
        [ ( "append"
          , EdhMethod
          , vecAppendProc
          , PackReceiver [mandatoryArg "values"]
          )
        , ("==", EdhMethod, vecEqProc     , PackReceiver [])
        , ("[]", EdhMethod, vecIdxReadProc, PackReceiver [mandatoryArg "idx"])
        , ( "[=]"
          , EdhMethod
          , vecIdxWriteProc
          , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
          )
        , ( "[+=]"
          , EdhMethod
          , vecIdxAssignWithOpProc addProc
          , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
          )
        , ( "[-=]"
          , EdhMethod
          , vecIdxAssignWithOpProc subtProc
          , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
          )
        , ( "[*=]"
          , EdhMethod
          , vecIdxAssignWithOpProc mulProc
          , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
          )
        , ( "[/=]"
          , EdhMethod
          , vecIdxAssignWithOpProc divProc
          , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
          )
        , ( "[//=]"
          , EdhMethod
          , vecIdxAssignWithOpProc divIntProc
          , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
          )
        , ( "[%=]"
          , EdhMethod
          , vecIdxAssignWithOpProc modIntProc
          , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
          )
        , ( "[**=]"
          , EdhMethod
          , vecIdxAssignWithOpProc powProc
          , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
          )
        , ( "[&&=]"
          , EdhMethod
          , vecIdxAssignWithOpProc logicalAndProc
          , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
          )
        , ( "[||=]"
          , EdhMethod
          , vecIdxAssignWithOpProc logicalOrProc
          , PackReceiver [mandatoryArg "idx", mandatoryArg "val"]
          )
        , ( "+"
          , EdhMethod
          , vecCopyWithOpProc addProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "-"
          , EdhMethod
          , vecCopyWithOpProc subtProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "*"
          , EdhMethod
          , vecCopyWithOpProc mulProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "/"
          , EdhMethod
          , vecCopyWithOpProc divProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "//"
          , EdhMethod
          , vecCopyWithOpProc divIntProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "%"
          , EdhMethod
          , vecCopyWithOpProc modIntProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "**"
          , EdhMethod
          , vecCopyWithOpProc powProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "&&"
          , EdhMethod
          , vecCopyWithOpProc logicalAndProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "||"
          , EdhMethod
          , vecCopyWithOpProc logicalOrProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "+="
          , EdhMethod
          , vecAssignWithOpProc addProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "-="
          , EdhMethod
          , vecAssignWithOpProc subtProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "*="
          , EdhMethod
          , vecAssignWithOpProc mulProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "/="
          , EdhMethod
          , vecAssignWithOpProc divProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "//="
          , EdhMethod
          , vecAssignWithOpProc divIntProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "%="
          , EdhMethod
          , vecAssignWithOpProc modIntProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "**="
          , EdhMethod
          , vecAssignWithOpProc powProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "&&="
          , EdhMethod
          , vecAssignWithOpProc logicalAndProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ( "||="
          , EdhMethod
          , vecAssignWithOpProc logicalOrProc
          , PackReceiver [mandatoryArg "val"]
          )
        , ("__null__", EdhMethod, vecNullProc, PackReceiver [])
        , ("__len__" , EdhMethod, vecLenProc , PackReceiver [])
        , ("__repr__", EdhMethod, vecReprProc, PackReceiver [])
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
        Just !len | len >= 0 -> doIt (fromInteger len) $ ctorArgs ++ repeat nil
        _ ->
          throwEdh etsCtor UsageError
            $  "length not an positive integer: "
            <> T.pack (show d)
      Just !badLenVal ->
        throwEdh etsCtor UsageError $ "invalid length: " <> T.pack
          (show badLenVal)

  vecAppendProc :: EdhHostProc
  vecAppendProc (ArgsPack !args !kwargs) !exit !ets = if not (odNull kwargs)
    then throwEdh ets UsageError "invalid args to Vector.append()"
    else withThisHostObj ets $ \ !hsv (mvec :: EdhVector) -> do
      !mvec' <-
        unsafeIOToSTM $ V.thaw =<< (V.++ V.fromList args) <$> V.freeze mvec
      writeTVar hsv $ toDyn mvec'
      exitEdh ets exit $ EdhObject $ edh'scope'this $ contextScope $ edh'context
        ets

  vecEqProc :: EdhHostProc
  vecEqProc (ArgsPack !args _kwargs) !exit !ets = case args of
    [EdhObject !objOther] -> withThisHostObj ets $ \_ (mvec :: EdhVector) ->
      withHostObject' objOther naExit $ \_ !mvecOther -> do
        !conclusion <- unsafeIOToSTM $ do
          -- TODO we're sacrificing thread safety for zero-copy performance
          --      here, justify this decision
          !vec      <- V.unsafeFreeze mvec
          !vecOther <- V.unsafeFreeze mvecOther
          return $ vec == vecOther
        exitEdh ets exit $ EdhBool conclusion
    _ -> naExit
    where naExit = exitEdh ets exit $ EdhBool False

  vecIdxReadProc :: EdhHostProc
  vecIdxReadProc apk@(ArgsPack !args _kwargs) !exit !ets = case args of
    [!idxVal] -> withHostObject ets thisVecObj $ \_ !mvec -> do
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

    _ -> throwEdh ets UsageError $ "invalid index for a Vector: " <> T.pack
      (show apk)
   where
    !scope      = contextScope $ edh'context ets
    !thisVecObj = edh'scope'this scope

  vecIdxWriteProc :: EdhHostProc
  vecIdxWriteProc apk@(ArgsPack !args _kwargs) !exit !ets = case args of
    [!idxVal, !other] -> withThisHostObj ets $ \_ !mvec -> do
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

    _ ->
      throwEdh ets UsageError
        $  "invalid assigning index for a Vector: "
        <> T.pack (show apk)


  vecCopyWithOpProc :: EdhIntrinsicOp -> EdhHostProc
  vecCopyWithOpProc !withOp apk@(ArgsPack !args _kwargs) !exit !ets =
    case args of
      [!other] -> withHostObject ets thisVecObj $ \_ !mvec ->
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
                  $ withOp (IntplSubs srcVal) (IntplSubs other)
                  $ \ !opRtnV _ets -> do
                      unsafeIOToSTM $ MV.unsafeWrite newVec n opRtnV
                      copyAt (n - 1)
          in
            copyAt (MV.length mvec - 1)
      _ ->
        throwEdh ets UsageError
          $  "invalid op assigning args for a Vector: "
          <> T.pack (show apk)
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
          $ withOp (IntplSubs oldVal) (IntplSubs rhVal)
          $ \ !opRtnV _ets -> do
              unsafeIOToSTM $ MV.unsafeWrite mvec n opRtnV
              assignAt (n + step)

  vecAssignWithOpProc :: EdhIntrinsicOp -> EdhHostProc
  vecAssignWithOpProc !withOp apk@(ArgsPack !args _kwargs) !exit !ets =
    case args of
      [!other] -> withHostObject ets thisVecObj $ \_ !mvec ->
        opAssignElems ets withOp other mvec 0 (MV.length mvec) 1
          $ exitEdh ets exit
          $ EdhObject thisVecObj
      _ ->
        throwEdh ets UsageError
          $  "invalid op assigning args for a Vector: "
          <> T.pack (show apk)
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
          $ withOp (IntplSubs oldVal) (IntplSubs x)
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
          $ withOp (IntplSubs oldVal) (IntplSubs otherVal)
          $ \ !opRtnV _ets -> do
              unsafeIOToSTM $ MV.unsafeWrite mvec n opRtnV
              assignWithVec (n + step) (i + 1) mvec'

  vecIdxAssignWithOpProc :: EdhIntrinsicOp -> EdhHostProc
  vecIdxAssignWithOpProc !withOp apk@(ArgsPack !args _kwargs) !exit !ets =
    case args of
      [!idxVal, !other] -> withThisHostObj ets $ \_ !mvec ->
        parseEdhIndex ets idxVal $ \case
          Left !err -> throwEdh ets UsageError err
          Right (EdhIndex !i) ->
            unsafeIOToSTM (MV.read mvec i) >>= \ !oldVal ->
              runEdhTx ets
                $ withOp (IntplSubs oldVal) (IntplSubs other)
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

      _ ->
        throwEdh ets UsageError
          $  "invalid index op assigning args for a Vector: "
          <> T.pack (show apk)


  vecNullProc :: EdhHostProc
  vecNullProc _ !exit !ets = withThisHostObj ets $ \_ (mvec :: EdhVector) ->
    exitEdh ets exit $ EdhBool $ MV.length mvec <= 0

  vecLenProc :: EdhHostProc
  vecLenProc _ !exit !ets = withThisHostObj ets $ \_ (mvec :: EdhVector) ->
    exitEdh ets exit $ EdhDecimal $ fromIntegral $ MV.length mvec

  vecReprProc :: EdhHostProc
  vecReprProc _ !exit !ets = withThisHostObj ets $ \_ (mvec :: EdhVector) -> do
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

