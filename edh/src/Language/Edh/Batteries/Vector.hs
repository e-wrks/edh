
module Language.Edh.Batteries.Vector where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad.Reader
import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map
import           Data.Dynamic

import           Data.Vector.Mutable            ( IOVector )
import qualified Data.Vector                   as V
import qualified Data.Vector.Mutable           as MV

import qualified Data.Lossless.Decimal         as D

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | host constructor Vector(*elements,length=None)
vecHostCtor :: EdhHostCtor
vecHostCtor !pgsCtor (ArgsPack !ctorArgs !ctorKwargs) !ctorExit = do
  let doIt :: Int -> [EdhValue] -> STM ()
      -- note @vs@ got to be lazy
      doIt !len vs = do
        let !vec = case len of
              _ | len < 0 -> V.fromList vs
              _           -> V.fromListN len vs
        !mvec <- unsafeIOToSTM $ V.thaw vec
        ctorExit $ toDyn mvec
  case Map.lookup (AttrByName "length") ctorKwargs of
    Nothing              -> doIt (-1) ctorArgs
    Just (EdhDecimal !d) -> case D.decimalToInteger d of
      Just !len | len >= 0 -> doIt (fromInteger len) $ ctorArgs ++ repeat nil
      _ ->
        throwEdhSTM pgsCtor UsageError
          $  "Length not an positive integer: "
          <> T.pack (show d)
    Just !badLenVal ->
      throwEdhSTM pgsCtor UsageError $ "Invalid length: " <> T.pack
        (show badLenVal)

vecMethods :: EdhProgState -> STM [(AttrKey, EdhValue)]
vecMethods !pgsModule = sequence
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
    , ("length"  , EdhMethod, vecLenProc , PackReceiver [])
    , ("__repr__", EdhMethod, vecReprProc, PackReceiver [])
    ]
  ]
 where
  !scope = contextScope $ edh'context pgsModule

  vecAppendProc :: EdhProcedure
  vecAppendProc (ArgsPack !args !kwargs) !exit | Map.null kwargs = do
    pgs <- ask
    let
      !that = thatObject $ contextScope $ edh'context pgs
      esClone :: Dynamic -> (Dynamic -> STM ()) -> STM ()
      esClone !esd !cloneTo = case fromDynamic esd of
        Nothing                  -> cloneTo $ toDyn nil
        Just (mvec :: EdhVector) -> do
          mvec' <-
            unsafeIOToSTM $ V.thaw =<< (V.++ V.fromList args) <$> V.freeze mvec
          cloneTo $ toDyn mvec'
    contEdhSTM $ cloneEdhObject that esClone $ exitEdhSTM pgs exit . EdhObject
  vecAppendProc _ _ = throwEdh UsageError "Invalid args to Vector.append()"

  vecEqProc :: EdhProcedure
  vecEqProc (ArgsPack [EdhObject (Object !entOther _ _)] !kwargs) !exit
    | Map.null kwargs = withThatEntity $ \ !pgs !mvec ->
      fromDynamic <$> readTVar (entity'store entOther) >>= \case
        Nothing                       -> exitEdhSTM pgs exit $ EdhBool False
        Just (mvecOther :: EdhVector) -> do
          !conclusion <- unsafeIOToSTM $ do
            -- TODO we're sacrificing thread safety for zero-copy performance
            --      here, justify this decision
            vec      <- V.unsafeFreeze mvec
            vecOther <- V.unsafeFreeze mvecOther
            return $ vec == vecOther
          exitEdhSTM pgs exit $ EdhBool conclusion
  vecEqProc _ !exit = exitEdhProc exit $ EdhBool False


  vecIdxReadProc :: EdhProcedure
  vecIdxReadProc (ArgsPack [!idxVal] !kwargs) !exit | Map.null kwargs =
    withThatEntity $ \ !pgs !mvec -> do
      let vecObj = thatObject $ contextScope $ edh'context pgs
          exitWith :: IOVector EdhValue -> STM ()
          exitWith !newVec =
            cloneEdhObject vecObj (\_ !cloneTo -> cloneTo $ toDyn newVec)
              $ \ !newObj -> exitEdhSTM pgs exit $ EdhObject newObj
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

      parseEdhIndex pgs idxVal $ \case
        Left !err -> throwEdhSTM pgs UsageError err
        Right (EdhIndex !i) ->
          unsafeIOToSTM (MV.read mvec i) >>= exitEdhSTM pgs exit
        Right EdhAny -> exitEdhSTM pgs exit $ EdhObject vecObj
        Right EdhAll -> exitEdhSTM pgs exit $ EdhObject vecObj
        Right (EdhSlice !start !stop !step) ->
          edhRegulateSlice pgs (MV.length mvec) (start, stop, step)
            $ \(!iStart, !iStop, !iStep) -> if iStep == 1
                then exitWith $ MV.unsafeSlice iStart (iStop - iStart) mvec
                else exitWithRange iStart iStop iStep

  vecIdxReadProc !apk _ =
    throwEdh UsageError $ "Invalid index for a Vector: " <> T.pack (show apk)

  vecIdxWriteProc :: EdhProcedure
  vecIdxWriteProc (ArgsPack [!idxVal, !other] !kwargs) !exit | Map.null kwargs =
    withThatEntity $ \ !pgs !mvec -> do
      let exitWithRangeAssign :: Int -> Int -> Int -> STM ()
          exitWithRangeAssign !start !stop !step = case edhUltimate other of
            EdhObject !otherObj ->
              fromDynamic
                <$> readTVar (entity'store $ objEntity otherObj)
                >>= \case
                      Just (mvecOther :: IOVector EdhValue) -> do
                        unsafeIOToSTM $ assignWithVec start 0 mvecOther
                        exitEdhSTM pgs exit other
                      Nothing -> exitWithNonVecAssign
            _ -> exitWithNonVecAssign
           where
            (q, r)               = quotRem (stop - start) step
            !len                 = if r == 0 then abs q else 1 + abs q
            exitWithNonVecAssign = case edhUltimate other of
              EdhArgsPack (ArgsPack !args _) -> do
                unsafeIOToSTM $ assignWithList start $ take len args
                exitEdhSTM pgs exit other
              EdhList (List _ !lsv) -> do
                ls <- readTVar lsv
                unsafeIOToSTM $ assignWithList start $ take len ls
                exitEdhSTM pgs exit other
              !badList ->
                throwEdhSTM pgs UsageError
                  $  "Not assignable to indexed vector: "
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

      parseEdhIndex pgs idxVal $ \case
        Left  !err          -> throwEdhSTM pgs UsageError err
        Right (EdhIndex !i) -> do
          unsafeIOToSTM $ MV.unsafeWrite mvec i other
          exitEdhSTM pgs exit other
        Right EdhAny -> do
          unsafeIOToSTM $ MV.set mvec other
          exitEdhSTM pgs exit other
        Right EdhAll -> exitWithRangeAssign 0 (MV.length mvec) 1
        Right (EdhSlice !start !stop !step) ->
          edhRegulateSlice pgs (MV.length mvec) (start, stop, step)
            $ \(!iStart, !iStop, !iStep) ->
                exitWithRangeAssign iStart iStop iStep

  vecIdxWriteProc !apk _ =
    throwEdh UsageError $ "Invalid assigning index for a Vector: " <> T.pack
      (show apk)


  vecNullProc :: EdhProcedure
  vecNullProc _ !exit = withThatEntity $ \ !pgs (mvec :: EdhVector) ->
    exitEdhSTM pgs exit $ EdhBool $ MV.length mvec <= 0

  vecLenProc :: EdhProcedure
  vecLenProc _ !exit = withThatEntity $ \ !pgs (mvec :: EdhVector) ->
    exitEdhSTM pgs exit $ EdhDecimal $ fromIntegral $ MV.length mvec

  vecReprProc :: EdhProcedure
  vecReprProc _ !exit = withThatEntity $ \ !pgs !mvec -> do
    let go :: [EdhValue] -> [Text] -> STM ()
        go [] !rs =
          exitEdhSTM pgs exit
            $  EdhString
            $  "Vector("
            <> T.intercalate "," (reverse rs)
            <> ")"
        go (v : rest) rs = edhValueReprSTM pgs v $ \ !r -> go rest (r : rs)
    !vec <- unsafeIOToSTM $ V.freeze mvec
    go (V.toList vec) []

