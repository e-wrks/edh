
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
    [!idxVal] -> withThisHostObj ets $ \_ !mvec -> do
      let exitWith :: EdhVector -> STM ()
          exitWith !newVec = do
            !newStore <- HostStore <$> newTVar (toDyn newVec)
            cloneEdhObject thisVecObj (edh'scope'that scope) newStore
              >>= exitEdh ets exit
              .   EdhObject
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

