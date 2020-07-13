
module Language.Edh.Batteries.Vector where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad.Reader
import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map
import           Data.Maybe
import           Data.Dynamic

import           Data.Vector.Mutable            ( IOVector )
import qualified Data.Vector                   as V
import qualified Data.Vector.Mutable           as MV

import qualified Data.Lossless.Decimal         as D

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- Boxed Vector for Edh values, mutable anytime
type EdhVector = IOVector EdhValue

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
      let
        vecObj = thatObject $ contextScope $ edh'context pgs
        exitWith :: IOVector EdhValue -> STM ()
        exitWith !newVec =
          cloneEdhObject vecObj (\_ !cloneTo -> cloneTo $ toDyn newVec)
            $ \ !newObj -> exitEdhSTM pgs exit $ EdhObject newObj
        exitWithRange :: Int -> Int -> Int -> STM ()
        exitWithRange !start !stop !step = (exitWith =<<) $ unsafeIOToSTM $ do
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

      parseEdhIndex pgs idxVal $ \case
        Left !err -> throwEdhSTM pgs UsageError err
        Right (EdhIndex !i) ->
          unsafeIOToSTM (MV.read mvec i) >>= exitEdhSTM pgs exit
        Right EdhAny -> exitEdhSTM pgs exit $ EdhObject vecObj
        Right EdhAll -> exitEdhSTM pgs exit $ EdhObject vecObj
        Right (EdhSlice !start !stop !step) -> do
          let !len = MV.length mvec
          edhRegulateIndex pgs len (fromMaybe 0 start) $ \ !iStart ->
            edhRegulateIndex pgs len (fromMaybe len stop) $ \ !iStop ->
              if iStop == iStart
                then do
                  newVec <- unsafeIOToSTM $ MV.new 0
                  exitWith newVec
                else if iStop > iStart && (fromMaybe 1 step == 1)
                  then exitWith $ MV.unsafeSlice iStart (iStop - iStart) mvec
                  else case step of
                    Nothing -> exitWithRange iStart iStop
                      $ if iStop > iStart then 1 else -1
                    Just !iStep ->
                      if (iStop > iStart && iStep <= 0)
                         || (iStop < iStart && iStep >= 0)
                      then
                        throwEdhSTM pgs
                                    UsageError
                                    "Slice range is not converging"
                      else
                        exitWithRange iStart iStop iStep

  vecIdxReadProc !apk _ =
    throwEdh UsageError $ "Invalid index for a Vector: " <> T.pack (show apk)

  vecIdxWriteProc :: EdhProcedure
  vecIdxWriteProc (ArgsPack [!idxVal, !other] !kwargs) !exit | Map.null kwargs =
    withThatEntity $ \ !pgs !mvec -> do
      let exitWithRangeAssign :: Int -> Int -> Int -> STM ()
          exitWithRangeAssign !start !stop !step =
            (>> exitEdhSTM pgs exit other) $ case edhUltimate other of
              EdhObject !otherObj ->
                fromDynamic
                  <$> readTVar (entity'store $ objEntity otherObj)
                  >>= \case
                        Just (mvecOther :: IOVector EdhValue) ->
                          unsafeIOToSTM $ assignWithVec start 0 mvecOther
                        Nothing -> assignWithNonVec
              _ -> assignWithNonVec
           where
            (q, r)           = quotRem (stop - start) step
            !len             = if r == 0 then abs q else 1 + abs q
            assignWithNonVec = case edhUltimate other of
              EdhArgsPack (ArgsPack !args _) ->
                unsafeIOToSTM $ assignWithList start $ take len args
              EdhList (List _ !lsv) -> do
                ls <- readTVar lsv
                unsafeIOToSTM $ assignWithList start $ take len ls
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
        Right (EdhSlice !start !stop !step) -> do
          let !len = MV.length mvec
          edhRegulateIndex pgs len (fromMaybe 0 start) $ \ !iStart ->
            edhRegulateIndex pgs len (fromMaybe len stop) $ \ !iStop ->
              if iStop == iStart
                then exitEdhSTM pgs exit other
                else case step of
                  Nothing ->
                    exitWithRangeAssign iStart iStop
                      $ if iStop > iStart then 1 else -1
                  Just !iStep ->
                    if (iStop > iStart && iStep <= 0)
                       || (iStop < iStart && iStep >= 0)
                    then
                      throwEdhSTM pgs UsageError "Slice range is not converging"
                    else
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


edhRegulateSlice
  :: EdhProgState
  -> Int
  -> (Maybe Int, Maybe Int, Maybe Int)
  -> ((Int, Int, Int) -> STM ())
  -> STM ()
edhRegulateSlice !pgs !len (!start, !stop, !step) !exit = case step of
  Nothing -> case start of
    Nothing -> case stop of
      Nothing     -> exit (0, len, 1)

      -- (Any:iStop:Any)
      Just !iStop -> if iStop < 0
        then
          let iStop' = len + iStop
          in  if iStop' < 0
                then
                  throwEdhSTM pgs UsageError
                  $  "Stop index out of bounds: "
                  <> T.pack (show iStop)
                  <> " vs "
                  <> T.pack (show len)
                else exit (0, iStop', 1)
        else if iStop > len
          then
            throwEdhSTM pgs EvalError
            $  "Stop index out of bounds: "
            <> T.pack (show iStop)
            <> " vs "
            <> T.pack (show len)
          else exit (0, iStop, 1)

    Just !iStart -> case stop of

      -- (iStart:Any:Any)
      Nothing -> if iStart < 0
        then
          let iStart' = len + iStart
          in  if iStart' < 0
                then
                  throwEdhSTM pgs UsageError
                  $  "Start index out of bounds: "
                  <> T.pack (show iStart)
                  <> " vs "
                  <> T.pack (show len)
                else exit (iStart', len, 1)
        else if iStart > len
          then
            throwEdhSTM pgs UsageError
            $  "Start index out of bounds: "
            <> T.pack (show iStart)
            <> " vs "
            <> T.pack (show len)
          else exit (iStart, len, 1)

      -- (iStart:iStop:Any)
      Just !iStop -> undefined

  Just !iStep -> if iStep == 0
    then throwEdhSTM pgs UsageError "Step is zero in slice"
    else if iStep < 0
      then case start of
        Nothing -> case stop of

          -- (Any:Any: -n)
          Nothing     -> undefined

          -- (Any:iStop: -n)
          Just !iStop -> undefined

        Just !iStart -> case stop of
          -- (iStart:Any: -n)
          Nothing     -> undefined

          -- (iStart:iStop: -n)
          Just !iStop -> undefined
      else case start of
        Nothing -> case stop of

          -- (Any:Any:n)
          Nothing     -> undefined

          -- (Any:iStop:n)
          Just !iStop -> undefined

        Just !iStart -> case stop of
          -- (iStart:Any:n)
          Nothing     -> undefined

          -- (iStart:iStop:n)
          Just !iStop -> undefined

