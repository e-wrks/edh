module Language.Edh.Batteries.Sema where

import Control.Applicative
import Control.Concurrent
import Control.Concurrent.STM
import Control.Monad
import qualified Data.Lossless.Decimal as D
import qualified Data.Text as T
import Language.Edh.Args
import Language.Edh.Batteries.InterOp
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.RtTypes
import Prelude

type EdhSema = TMVar Int

createSemaClass :: Scope -> STM Object
createSemaClass !clsOuterScope =
  mkHostClass clsOuterScope "Semaphore" (allocEdhObj semaAllocator) [] $
    \ !clsScope -> do
      !mths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ("waitAny", EdhMethod, wrapHostProc semaWaitAnyProc),
                  ("wait", EdhMethod, wrapHostProc semaWaitProc),
                  ("clear", EdhMethod, wrapHostProc semaClearProc),
                  ("put", EdhMethod, wrapHostProc semaPutProc),
                  ("inc", EdhMethod, wrapHostProc semaIncProc),
                  ("dec", EdhMethod, wrapHostProc semaDecProc),
                  ("__null__", EdhMethod, wrapHostProc semaNullProc),
                  ("__len__", EdhMethod, wrapHostProc semaInvGetter),
                  ("__repr__", EdhMethod, wrapHostProc semaReprProc)
                ]
          ]
            ++ [ (AttrByName nm,) <$> mkHostProperty clsScope nm getter setter
                 | (nm, getter, setter) <-
                     [ ("inv", semaInvGetter, Just semaInvSetter)
                     ]
               ]
      iopdUpdate mths $ edh'scope'entity clsScope
  where
    semaAllocator :: "initial" ?: Int -> EdhObjectAllocator
    semaAllocator (optionalArg -> !maybeInitial) !ctorExit _etsCtor =
      case maybeInitial of
        Just i | i > 0 -> do
          !sema <- newTMVar i
          ctorExit . HostStore =<< pinHostValue sema
        _ -> do
          !sema <- newEmptyTMVar @Int
          ctorExit . HostStore =<< pinHostValue sema

    semaWaitAnyProc :: EdhHostProc
    semaWaitAnyProc !exit !ets =
      withThisHostObj @EdhSema ets $ \ !sema -> runEdhTx ets $
        edhContSTM $ do
          !i <- takeTMVar sema
          exitEdh ets exit $ EdhDecimal $ fromIntegral i

    semaWaitProc :: "consume" ?: Int -> "timeout" ?: Int -> EdhHostProc
    semaWaitProc
      (defaultArg 1 -> !iConsume)
      (optionalArg -> !maybeTimeout)
      !exit
      !ets = withThisHostObj @EdhSema ets $ \ !sema -> do
        let doWait :: STM () -> STM ()
            doWait !overdueChk =
              if
                  | iConsume > 0 -> do
                    let tryConsume :: EdhTx
                        -- use `edhContSTM` to cooperate with perceivers
                        tryConsume = edhContSTM $
                          (overdueChk `orElse`) $ do
                            !i <- takeTMVar sema
                            let !iAvail = max 0 i
                                !iNew = iAvail - iConsume
                            if iNew < 0
                              then do
                                -- no enough inventory to consume,
                                -- put it back and wait another round for more
                                putTMVar sema i
                                runEdhTx ets tryConsume
                              else do
                                -- consume specified count
                                when (iNew > 0) $ putTMVar sema iNew
                                exitEdh ets exit $ EdhDecimal $ fromIntegral iNew
                    runEdhTx ets tryConsume
                  | iConsume == 0 -> runEdhTx ets $
                    edhContSTM $ do
                      !i <- readTMVar sema
                      exitEdh ets exit $ EdhDecimal $ fromIntegral i
                  | otherwise ->
                    throwEdh ets UsageError $
                      "invalid consumption of semaphore inventory: "
                        <> T.pack (show iConsume)
        case maybeTimeout of
          Just timeout | timeout > 0 -> runEdhTx ets $
            edhContIO $ do
              !overdueResult <- newEmptyTMVarIO
              void $
                forkFinally (threadDelay timeout) $
                  const $ atomically $ void $ tryPutTMVar overdueResult EdhNil
              atomically $
                doWait $ takeTMVar overdueResult >>= exitEdh ets exit
          _ ->
            doWait retry

    semaClearProc :: EdhHostProc
    semaClearProc !exit !ets = withThisHostObj @EdhSema ets $ \ !sema ->
      tryTakeTMVar sema >>= \case
        Nothing -> exitEdh ets exit $ EdhDecimal 0
        Just i -> exitEdh ets exit $ EdhDecimal $ fromIntegral $ max 0 i

    semaPutProc :: "inv" !: Int -> EdhHostProc
    semaPutProc (mandatoryArg -> !iNew) !exit !ets =
      withThisHostObj @EdhSema ets $ \ !sema ->
        if
            | iNew > 0 ->
              tryTakeTMVar sema >>= \case
                Nothing -> do
                  putTMVar sema iNew
                  exitEdh ets exit $ EdhDecimal 0
                Just i -> do
                  putTMVar sema iNew
                  exitEdh ets exit $ EdhDecimal $ fromIntegral $ max 0 i
            | iNew == 0 ->
              tryTakeTMVar sema >>= \case
                Nothing -> exitEdh ets exit $ EdhDecimal 0
                Just i ->
                  exitEdh ets exit $ EdhDecimal $ fromIntegral $ max 0 i
            | otherwise ->
              throwEdh ets UsageError $
                "invalid semaphore inventory to put: " <> T.pack (show iNew)

    semaIncProc :: "chg" ?: Int -> EdhHostProc
    semaIncProc (defaultArg 1 -> !iChg) !exit !ets =
      withThisHostObj @EdhSema ets $ \ !sema ->
        if
            | iChg > 0 ->
              tryTakeTMVar sema >>= \case
                Nothing -> do
                  putTMVar sema iChg
                  exitEdh ets exit $ EdhDecimal 0
                Just i -> do
                  let !iOld = max 0 i
                  putTMVar sema $ iOld + iChg
                  exitEdh ets exit $ EdhDecimal $ fromIntegral iOld
            | iChg == 0 ->
              tryReadTMVar sema >>= \case
                Nothing -> exitEdh ets exit $ EdhDecimal 0
                Just i -> do
                  let !iOld = max 0 i
                  exitEdh ets exit $ EdhDecimal $ fromIntegral iOld
            | otherwise ->
              throwEdh ets UsageError $
                "invalid increment to semaphore inventory: "
                  <> T.pack (show iChg)

    semaDecProc :: "chg" ?: Int -> EdhHostProc
    semaDecProc (defaultArg 1 -> !iChg) !exit !ets =
      withThisHostObj @EdhSema ets $ \ !sema ->
        if
            | iChg > 0 ->
              tryTakeTMVar sema >>= \case
                Nothing -> exitEdh ets exit $ EdhDecimal 0
                Just i -> do
                  let !iOld = max 0 i
                      !iNew = iOld - iChg
                  if iNew > 0
                    then do
                      putTMVar sema iNew
                      exitEdh ets exit $ EdhDecimal $ fromIntegral iOld
                    else exitEdh ets exit $ EdhDecimal $ fromIntegral iOld
            | iChg == 0 ->
              tryReadTMVar sema >>= \case
                Nothing -> exitEdh ets exit $ EdhDecimal 0
                Just i -> do
                  let !iOld = max 0 i
                  exitEdh ets exit $ EdhDecimal $ fromIntegral iOld
            | otherwise ->
              throwEdh ets UsageError $
                "invalid decrement to semaphore inventory: "
                  <> T.pack (show iChg)

    semaNullProc :: EdhHostProc
    semaNullProc !exit !ets = withThisHostObj @EdhSema ets $ \ !sema ->
      tryReadTMVar sema >>= \case
        Nothing -> exitEdh ets exit $ EdhBool True
        Just i -> exitEdh ets exit $ EdhBool $ i <= 0

    semaReprProc :: EdhHostProc
    semaReprProc !exit !ets = withThisHostObj @EdhSema ets $ \ !sema ->
      tryReadTMVar sema >>= \case
        Nothing -> exitEdh ets exit $ EdhString "Semaphore()"
        Just i ->
          exitEdh ets exit $ EdhString $ "Semaphore(" <> T.pack (show i) <> ")"

    semaInvGetter :: EdhHostProc
    semaInvGetter !exit !ets = withThisHostObj @EdhSema ets $ \ !sema ->
      tryReadTMVar sema >>= \case
        Nothing -> exitEdh ets exit $ EdhDecimal 0
        Just i -> exitEdh ets exit $ EdhDecimal $ fromIntegral $ max 0 i

    semaInvSetter :: Maybe EdhValue -> EdhHostProc
    semaInvSetter Nothing !exit = semaClearProc $ \_ ->
      -- to maintain intuition in chained assignment
      exitEdhTx exit EdhNil
    semaInvSetter (Just invVal) !exit = case edhUltimate invVal of
      EdhDecimal invD -> case D.decimalToInteger invD of
        Just inv | inv >= 0 -> semaPutProc (NamedEdhArg $ fromInteger inv) $
          -- to maintain intuition in chained assignment
          \_ -> exitEdhTx exit invVal
        _ -> badVal
      _ -> badVal
      where
        badVal = edhValueDescTx invVal $ \badDesc ->
          throwEdhTx UsageError $
            "invalid semaphore inventory to set: " <> badDesc
