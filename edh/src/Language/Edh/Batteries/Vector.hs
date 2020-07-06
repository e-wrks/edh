
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
      esClone !esd !exit' = case fromDynamic esd of
        Nothing                  -> exit' $ toDyn nil
        Just (mvec :: EdhVector) -> do
          mvec' <-
            unsafeIOToSTM $ V.thaw =<< (V.++ V.fromList args) <$> V.freeze mvec
          exit' $ toDyn mvec'
    contEdhSTM $ cloneEdhObject that esClone $ exitEdhSTM pgs exit . EdhObject
  vecAppendProc _ _ = throwEdh UsageError "Invalid args to Vector.append()"

  vecEqProc :: EdhProcedure
  vecEqProc (ArgsPack [EdhObject (Object !entOther _ _)] !kwargs) !exit
    | Map.null kwargs = withThatEntityStore $ \ !pgs !mvec ->
      fromDynamic <$> readTVar (entity'store entOther) >>= \case
        Nothing                       -> exitEdhSTM pgs exit $ EdhBool False
        Just (mvecOther :: EdhVector) -> do
          !conclusion <- unsafeIOToSTM $ do
            -- TODO we're sacrificing thread safety for performance here
            --      justify this decision
            vec      <- V.unsafeFreeze mvec
            vecOther <- V.unsafeFreeze mvecOther
            return $ vec == vecOther
          exitEdhSTM pgs exit $ EdhBool conclusion
  vecEqProc _ !exit = exitEdhProc exit $ EdhBool False

  vecIdxReadProc :: EdhProcedure
  vecIdxReadProc (ArgsPack !args !_kwargs) !exit =
    withThatEntityStore $ \ !pgs !mvec -> case args of
      [EdhDecimal !idx] -> case fromInteger <$> D.decimalToInteger idx of
        Just !n -> edhRegulateIndex pgs (MV.length mvec) n
          $ \ !i -> (unsafeIOToSTM $ MV.read mvec i) >>= exitEdhSTM pgs exit
        _ ->
          throwEdhSTM pgs UsageError $ "Not an integer for index: " <> T.pack
            (show idx)
      -- TODO support slicing
      _ -> throwEdhSTM pgs UsageError "Invalid index for a Vector"

  vecIdxWriteProc :: EdhProcedure
  vecIdxWriteProc (ArgsPack !args !_kwargs) !exit =
    withThatEntityStore $ \ !pgs !mvec -> case args of
      [EdhDecimal !idx, !val] -> case fromInteger <$> D.decimalToInteger idx of
        Just !n -> edhRegulateIndex pgs (MV.length mvec) n $ \ !i ->
          unsafeIOToSTM (MV.write mvec i val) >> exitEdhSTM pgs exit val
        _ ->
          throwEdhSTM pgs UsageError $ "Not an integer for index: " <> T.pack
            (show idx)
      -- TODO support slicing
      _ -> throwEdhSTM pgs UsageError "Invalid index for a Vector"

  vecNullProc :: EdhProcedure
  vecNullProc _ !exit = withThatEntityStore $ \ !pgs (mvec :: EdhVector) ->
    exitEdhSTM pgs exit $ EdhBool $ MV.length mvec <= 0

  vecLenProc :: EdhProcedure
  vecLenProc _ !exit = withThatEntityStore $ \ !pgs (mvec :: EdhVector) ->
    exitEdhSTM pgs exit $ EdhDecimal $ fromIntegral $ MV.length mvec

  vecReprProc :: EdhProcedure
  vecReprProc _ !exit = withThatEntityStore $ \ !pgs !mvec -> do
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

