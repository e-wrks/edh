
module Language.Edh.Batteries.Vector where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad.Reader
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
import           Language.Edh.Details.Evaluate


-- Boxed Vector for Edh values, non-transactional, mutable anytime
type EdhVector = IOVector EdhValue


-- | host constructor Vector(*elements,length=None)
vecHostCtor :: EdhHostCtor
vecHostCtor !etsCtor (ArgsPack !ctorArgs !ctorKwargs) !ctorExit = do
  let doIt :: Int -> [EdhValue] -> STM ()
      -- note @vs@ got to be lazy
      doIt !len vs = do
        let !vec = case len of
              _ | len < 0 -> V.fromList vs
              _           -> V.fromListN len vs
        !mvec <- unsafeIOToSTM $ V.thaw vec
        ctorExit $ toDyn mvec
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

vecMethods :: EdhThreadState -> STM [(AttrKey, EdhValue)]
vecMethods !etsModule = sequence
  [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp mthArgs
  | (nm, vc, hp, mthArgs) <-
    [ ("append", EdhMethod, vecAppendProc, PackReceiver [mandatoryArg "values"])
    , ("=="    , EdhMethod, vecEqProc     , PackReceiver [])
    , ("[]"    , EdhMethod, vecIdxReadProc, PackReceiver [mandatoryArg "idx"])
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
 where
  !scope = contextScope $ edh'context etsModule

  vecAppendProc :: EdhHostProc
  vecAppendProc (ArgsPack !args !kwargs) !exit | odNull kwargs = do
    ets <- ask
    let
      !that = thatObject $ contextScope $ edh'context ets
      esClone :: Dynamic -> (Dynamic -> STM ()) -> STM ()
      esClone !esd !cloneTo = case fromDynamic esd of
        Nothing                  -> cloneTo $ toDyn nil
        Just (mvec :: EdhVector) -> do
          mvec' <-
            unsafeIOToSTM $ V.thaw =<< (V.++ V.fromList args) <$> V.freeze mvec
          cloneTo $ toDyn mvec'
    contEdhSTM $ cloneEdhObject that esClone $ exitEdh ets exit . EdhObject
  vecAppendProc _ _ = throwEdh UsageError "invalid args to Vector.append()"

  vecEqProc :: EdhHostProc
  vecEqProc (ArgsPack [EdhObject (Object !entOther _ _)] !kwargs) !exit
    | odNull kwargs = withThatEntity $ \ !ets !mvec ->
      fromDynamic <$> readTVar (entity'store entOther) >>= \case
        Nothing                       -> exitEdh ets exit $ EdhBool False
        Just (mvecOther :: EdhVector) -> do
          !conclusion <- unsafeIOToSTM $ do
            -- TODO we're sacrificing thread safety for zero-copy performance
            --      here, justify this decision
            vec      <- V.unsafeFreeze mvec
            vecOther <- V.unsafeFreeze mvecOther
            return $ vec == vecOther
          exitEdh ets exit $ EdhBool conclusion
  vecEqProc _ !exit = exitEdhTx exit $ EdhBool False


  vecIdxReadProc :: EdhHostProc
  vecIdxReadProc (ArgsPack [!idxVal] !kwargs) !exit | odNull kwargs =
    withThatEntity $ \ !ets !mvec -> do
      let vecObj = thatObject $ contextScope $ edh'context ets
          exitWith :: IOVector EdhValue -> STM ()
          exitWith !newVec =
            cloneEdhObject vecObj (\_ !cloneTo -> cloneTo $ toDyn newVec)
              $ \ !newObj -> exitEdh ets exit $ EdhObject newObj
          exitWithRange :: Int -> Int -> Int -> STM ()
          exitWithRange !start !stop !step = do
            !newVec <- unsafeIOToSTM $ do
              let (q, r) = quotRem (stop - start) step
                  !len   = if r == 0 then abs q else 1 + abs q
              newVec <- MV.new len
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
        Right EdhAny -> exitEdh ets exit $ EdhObject vecObj
        Right EdhAll -> exitEdh ets exit $ EdhObject vecObj
        Right (EdhSlice !start !stop !step) ->
          edhRegulateSlice ets (MV.length mvec) (start, stop, step)
            $ \(!iStart, !iStop, !iStep) -> if iStep == 1
                then exitWith $ MV.unsafeSlice iStart (iStop - iStart) mvec
                else exitWithRange iStart iStop iStep

  vecIdxReadProc !apk _ =
    throwEdh UsageError $ "invalid index for a Vector: " <> T.pack (show apk)

  vecIdxWriteProc :: EdhHostProc
  vecIdxWriteProc (ArgsPack [!idxVal, !other] !kwargs) !exit | odNull kwargs =
    withThatEntity $ \ !ets !mvec -> do
      let exitWithRangeAssign :: Int -> Int -> Int -> STM ()
          exitWithRangeAssign !start !stop !step = case edhUltimate other of
            EdhObject !otherObj ->
              fromDynamic
                <$> readTVar (entity'store $ objEntity otherObj)
                >>= \case
                      Just (mvecOther :: IOVector EdhValue) -> do
                        unsafeIOToSTM $ assignWithVec start 0 mvecOther
                        exitEdh ets exit other
                      Nothing -> exitWithNonVecAssign
            _ -> exitWithNonVecAssign
           where
            (q, r)               = quotRem (stop - start) step
            !len                 = if r == 0 then abs q else 1 + abs q
            exitWithNonVecAssign = case edhUltimate other of
              EdhArgsPack (ArgsPack !args _) -> do
                unsafeIOToSTM $ assignWithList start $ take len args
                exitEdh ets exit other
              EdhList (List _ !lsv) -> do
                ls <- readTVar lsv
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
            assignWithVec :: Int -> Int -> IOVector EdhValue -> IO ()
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

  vecIdxWriteProc !apk _ =
    throwEdh UsageError $ "invalid assigning index for a Vector: " <> T.pack
      (show apk)


  vecNullProc :: EdhHostProc
  vecNullProc _ !exit = withThatEntity $ \ !ets (mvec :: EdhVector) ->
    exitEdh ets exit $ EdhBool $ MV.length mvec <= 0

  vecLenProc :: EdhHostProc
  vecLenProc _ !exit = withThatEntity $ \ !ets (mvec :: EdhVector) ->
    exitEdh ets exit $ EdhDecimal $ fromIntegral $ MV.length mvec

  vecReprProc :: EdhHostProc
  vecReprProc _ !exit = withThatEntity $ \ !ets !mvec -> do
    let go :: [EdhValue] -> [Text] -> STM ()
        go [] !rs =
          exitEdh ets exit
            $  EdhString
            $  "Vector("
            <> T.intercalate "," (reverse rs)
            <> ")"
        go (v : rest) rs = edhValueReprSTM ets v $ \ !r -> go rest (r : rs)
    !vec <- unsafeIOToSTM $ V.freeze mvec
    go (V.toList vec) []

