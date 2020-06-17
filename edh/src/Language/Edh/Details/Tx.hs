
module Language.Edh.Details.Tx where

import           Prelude
import           Debug.Trace

import           Control.Exception
import           Control.Monad
import           Control.Monad.Reader

import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Dynamic

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | Edh follows GHC's program termination criteria that the main thread
-- decides all. see:
--   https://hackage.haskell.org/package/base/docs/Control-Concurrent.html
-- description at:
--   https://github.com/e-wrks/edh/tree/master/Tour#program--threading-model
driveEdhProgram
  :: TMVar (Either SomeException EdhValue) -> Context -> EdhProc -> IO ()
driveEdhProgram !haltResult !progCtx !prog = do
  -- check async exception mask state
  getMaskingState >>= \case
    Unmasked -> return ()
    _ ->
      throwIO
        $ EdhError UsageError
                   "Edh program should not run with async exceptions masked"
        $ EdhCallContext "<edh>" []

  -- prepare program environment
  !mainThId <- myThreadId
  let onDescendantExc :: SomeException -> IO ()
      onDescendantExc e = case asyncExceptionFromException e of
        Just (asyncExc :: SomeAsyncException) ->
          -- todo special handling here ?
          throwTo mainThId asyncExc
        _ -> throwTo mainThId e
  -- prepare the go routine forker
  !forkQueue <- newTBQueueIO 100
  let
    forkDescendants :: IO ()
    forkDescendants =
      atomically
          (        (Nothing <$ readTMVar haltResult)
          `orElse` (Just <$> readTBQueue forkQueue)
          )
        >>= \case
              Nothing               -> return () -- Edh program halted, done
              Just (pgsForker, job) -> do
                pgsDesc <- deriveState pgsForker
                -- bootstrap on the descendant thread
                atomically $ writeTBQueue (edh'task'queue pgsDesc) $ EdhTxTask
                  { edh'task'pgs   = pgsDesc
                  , edh'task'input = wuji pgsForker
                  , edh'task'job   = const job
                  }
                void $ mask_ $ forkIOWithUnmask $ \unmask -> catch
                  (unmask $ driveEdhThread (edh'defers pgsDesc)
                                           (edh'task'queue pgsDesc)
                  )
                  onDescendantExc
                -- keep the forker running
                forkDescendants
     where
      -- derive program state for the descendant thread
      deriveState :: EdhProgState -> IO EdhProgState
      deriveState !pgsFrom = do
        !descQueue  <- newTBQueueIO 200
        !perceivers <- newTVarIO []
        !defers     <- newTVarIO []
        return pgsFrom
          { edh'task'queue = descQueue
          , edh'perceivers = perceivers
          , edh'defers     = defers
          -- the forker should have checked not in tx, enforce here
          , edh'in'tx      = False
          -- don't be exporting or defining effects on a forked thread
          -- by default, the programmer must explicitly mark so
          , edh'context    = fromCtx { contextExporting   = False
                                     , contextEffDefining = False
                                     }
          }
        where !fromCtx = edh'context pgsFrom
  -- start forker thread
  void $ mask_ $ forkIOWithUnmask $ \unmask ->
    catch (unmask forkDescendants) onDescendantExc
  -- run the main thread
  flip finally
       (
        -- set halt result after the main thread done, anyway if not already,
        -- so all descendant threads will terminate. or else hanging STM jobs
        -- may cause the whole process killed by GHC deadlock detector.
        atomically $ void $ tryPutTMVar haltResult (Right nil)
        -- TODO is it good idea to let all live Edh threads go through
        --      ProgramHalt propagation? Their `defer` actions can do cleanup
        --      already, need such a chance with exception handlers too?
                                                              )
    $ handle
        (\(e :: SomeException) -> case fromException e :: Maybe EdhError of
          Just (ProgramHalt phd) -> case fromDynamic phd :: Maybe EdhValue of
            Just phv -> atomically $ void $ tryPutTMVar haltResult $ Right phv
            _        -> case fromDynamic phd :: Maybe SomeException of
              Just phe -> atomically $ void $ tryPutTMVar haltResult (Left phe)
              _        -> atomically $ void $ tryPutTMVar haltResult (Left e)
          Just _  -> atomically $ void $ tryPutTMVar haltResult (Left e)
          Nothing -> do
            atomically $ void $ tryPutTMVar haltResult (Left e)
            throwIO e -- re-throw if the exception is unknown
        )
    $ do
        -- prepare program state for main Edh thread
        !mainQueue  <- newTBQueueIO 300
        !perceivers <- newTVarIO []
        !defers     <- newTVarIO []
        let !pgsAtBoot = EdhProgState { edh'fork'queue = forkQueue
                                      , edh'task'queue = mainQueue
                                      , edh'perceivers = perceivers
                                      , edh'defers     = defers
                                      , edh'in'tx      = False
                                      , edh'context    = progCtx
                                      }
        -- bootstrap the program on main Edh thread
        atomically $ writeTBQueue mainQueue $ EdhTxTask pgsAtBoot
                                                        (wuji pgsAtBoot)
                                                        (const prog)
        -- drive the main Edh thread
        driveEdhThread defers mainQueue

 where

  nextTaskFromQueue :: TBQueue EdhTask -> STM (Maybe EdhTask)
  nextTaskFromQueue = orElse (Nothing <$ readTMVar haltResult) . tryReadTBQueue

  driveDefers :: [DeferRecord] -> IO ()
  driveDefers [] = return ()
  driveDefers ((!pgsDefer, !deferedProc) : restDefers) = do
    !deferPerceivers <- newTVarIO []
    !deferDefers     <- newTVarIO []
    !deferTaskQueue  <- newTBQueueIO 100
    atomically $ writeTBQueue deferTaskQueue $ EdhTxTask
      pgsDefer { edh'task'queue = deferTaskQueue
               , edh'perceivers = deferPerceivers
               , edh'defers     = deferDefers
               , edh'in'tx      = False
               }
      (wuji pgsDefer)
      (const deferedProc)
    driveEdhThread deferDefers deferTaskQueue
    driveDefers restDefers

  drivePerceiver :: EdhValue -> PerceiveRecord -> IO Bool
  drivePerceiver !ev (_, pgsOrigin, reactExpr) = do
    !breakThread <- newEmptyTMVarIO
    let
      !perceiverProc =
        local
            (\pgs ->
              pgs { edh'context = (edh'context pgs) { contextMatch = ev } }
            )
          $ evalExpr reactExpr
          $ \(OriginalValue !perceiverRtn _ _) -> do
              let doBreak = case perceiverRtn of
                    EdhBreak -> True -- terminate this thread
                    _        -> False
              contEdhSTM $ putTMVar breakThread doBreak
    !reactPerceivers <- newTVarIO []
    !reactDefers     <- newTVarIO []
    !reactTaskQueue  <- newTBQueueIO 100
    let !pgsPerceiver = pgsOrigin { edh'task'queue = reactTaskQueue
                                  , edh'perceivers = reactPerceivers
                                  , edh'defers     = reactDefers
                                  , edh'in'tx      = False
                                  }
    atomically $ writeTBQueue reactTaskQueue $ EdhTxTask pgsPerceiver
                                                         (wuji pgsPerceiver)
                                                         (const perceiverProc)
    driveEdhThread reactDefers reactTaskQueue
    atomically $ readTMVar breakThread
  drivePerceivers :: [(EdhValue, PerceiveRecord)] -> IO Bool
  drivePerceivers []               = return False
  drivePerceivers ((ev, r) : rest) = drivePerceiver ev r >>= \case
    True  -> return True
    False -> drivePerceivers rest

  driveEdhThread :: TVar [DeferRecord] -> TBQueue EdhTask -> IO ()
  driveEdhThread !defers !tq = atomically (nextTaskFromQueue tq) >>= \case
    Nothing -> -- this thread is done, run defers lastly
      readTVarIO defers >>= driveDefers
    Just (EdhIOTask !pgs !ioAct !job) -> do
      let
        -- during ioAct, perceivers won't fire, program termination won't stop
        -- this thread
        doIt = ioAct >>= \actResult ->
          atomically $ writeTBQueue tq $ EdhTxTask pgs (wuji pgs) $ const $ job
            actResult
      catch doIt $ \(e :: SomeException) ->
        atomically $ toEdhError pgs e $ \exv ->
          writeTBQueue tq
            $ EdhTxTask pgs (wuji pgs)
            $ const
            $ contEdhSTM
            $ edhThrowSTM pgs exv
      driveEdhThread defers tq -- loop another iteration for the thread
    Just (EdhSTMTask !pgs !stmAct !job) -> do
      let
        doIt = goSTM False pgs stmAct >>= \case
          Left{} -> -- terminate this thread, after running defers lastly
            readTVarIO defers >>= driveDefers
          Right !actResult -> do
            atomically
              $ writeTBQueue tq
              $ EdhTxTask pgs (wuji pgs)
              $ const
              $ job actResult
            driveEdhThread defers tq -- loop another iteration for the thread
      catch doIt $ \(e :: SomeException) -> do
        atomically $ toEdhError pgs e $ \exv ->
          writeTBQueue tq
            $ EdhTxTask pgs (wuji pgs)
            $ const
            $ contEdhSTM
            $ edhThrowSTM pgs exv
        driveEdhThread defers tq -- loop another iteration for the thread
    Just (EdhTxTask !pgsTask !input !task) ->
      goSTM True pgsTask (join $ runReaderT (task input) pgsTask) >>= \case
        Left{} -> -- terminate this thread, after running defers lastly
          readTVarIO defers >>= driveDefers
        Right{} -> -- loop another iteration for the thread
          driveEdhThread defers tq

  goSTM :: forall a . Bool -> EdhProgState -> STM a -> IO (Either () a)
  goSTM !trackRetry !pgsTask !taskJob = if trackRetry
    then trackSTM 0
    else waitSTM
   where
    callCtx = getEdhCallContext 0 pgsTask

    -- blocking wait not expected, track stm retries explicitly
    trackSTM :: Int -> IO (Either () a)
    trackSTM !rtc = do

      when -- todo increase the threshold of reporting?
           (rtc > 0) $ do
        -- trace out the retries so the end users can be aware of them
        tid <- myThreadId
        trace
            (  "🔙\n"
            <> show callCtx
            <> "🌀 "
            <> show tid
            <> " stm retry #"
            <> show rtc
            )
          $ return ()

      atomically ((Just <$> stmJob) `orElse` return Nothing) >>= \case
        Just Nothing -> return $ Left () -- to terminate as program halted
        Nothing -> -- stm failed, do a tracked retry
          trackSTM (rtc + 1)
        Just (Just (Right !result)) ->
          -- no perceiver has fired, the tx job has already been executed
          return $ Right result
        Just (Just (Left !gotevl)) -> drivePerceivers gotevl >>= \case
          True -> -- a perceiver is terminating this thread
            return $ Left ()
          False ->
            -- there've been one or more perceivers fired, the tx job have
            -- been skipped, as no perceiver is terminating the thread,
            -- continue with this tx job
            trackSTM rtc

    -- blocking wait expected, but keep perceivers firing along the way,
    -- and terminate with the Edh program if that's the case
    waitSTM :: IO (Either () a)
    waitSTM = atomically stmJob >>= \case
      Nothing -> return $ Left () -- to terminate as program halted
      Just (Right !result) ->
          -- no perceiver has fired, the tx job has already been executed
        return $ Right result
      Just (Left !gotevl) -> drivePerceivers gotevl >>= \case
        True -> -- a perceiver is terminating this thread
          return $ Left ()
        False ->
          -- there've been one or more perceivers fired, the tx job have
          -- been skipped, as no perceiver is terminating the thread,
          -- continue with this tx job
          waitSTM

    -- this is the STM work package, where perceivers can preempt the inline
    -- job on an Edh thread
    stmJob :: STM (Maybe (Either [(EdhValue, PerceiveRecord)] a))
    stmJob = tryReadTMVar haltResult >>= \case
      Just _ -> return Nothing -- program halted
      Nothing -> -- program still running
        (readTVar (edh'perceivers pgsTask) >>= perceiverChk []) >>= \gotevl ->
          if null gotevl
            then -- no perceiver fires, execute the tx job
                 Just . Right <$> taskJob
            else -- skip the tx job if at least one perceiver fires
                 return $ Just $ Left gotevl

    perceiverChk
      :: [(EdhValue, PerceiveRecord)]
      -> [PerceiveRecord]
      -> STM [(EdhValue, PerceiveRecord)]
    perceiverChk !gotevl []                     = return gotevl
    perceiverChk !gotevl (r@(evc, _, _) : rest) = tryReadTChan evc >>= \case
      Just !ev -> perceiverChk ((ev, r) : gotevl) rest
      Nothing  -> perceiverChk gotevl rest
