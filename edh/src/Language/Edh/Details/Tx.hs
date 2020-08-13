
module Language.Edh.Details.Tx where

import           Prelude
-- import           Debug.Trace

import           Control.Exception
import           Control.Monad

import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Dynamic

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes


-- | Uncaught exception in any thread (main or a descendant) will terminate the
-- whole Edh program, see:
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
              Nothing                       -> return () -- Edh program halted, done
              Just (!etsForker, !actForkee) -> do
                etsForkee <- deriveState etsForker
                -- bootstrap on the descendant thread
                atomically
                  $ writeTBQueue (edh'task'queue etsForkee)
                  $ EdhDoSTM etsForkee
                  $ actForkee etsForkee
                void $ mask_ $ forkIOWithUnmask $ \unmask -> catch
                  (unmask $ driveEdhThread (edh'defers etsForkee)
                                           (edh'task'queue etsForkee)
                  )
                  onDescendantExc
                -- keep the forker running
                forkDescendants
     where
      -- derive thread state for the descendant thread
      deriveState :: EdhThreadState -> IO EdhThreadState
      deriveState !etsForker = do
        !descQueue  <- newTBQueueIO 200
        !perceivers <- newTVarIO []
        !defers     <- newTVarIO []
        return EdhThreadState
          { edh'in'tx      = False
          , edh'task'queue = descQueue
          , edh'perceivers = perceivers
          , edh'defers     = defers
          -- forkee inherits call stack etc in the context from forker, so
          -- effect resolution and far-reaching exception handlers can work.
          , edh'context    = fromCtx { contextExporting   = False
                                     , contextEffDefining = False
                                     }
          , edh'fork'queue = edh'fork'queue etsForker
          }
        where !fromCtx = edh'context etsForker
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
        let !etsAtBoot = EdhThreadState { edh'in'tx      = False
                                        , edh'task'queue = mainQueue
                                        , edh'perceivers = perceivers
                                        , edh'defers     = defers
                                        , edh'context    = progCtx
                                        , edh'fork'queue = forkQueue
                                        }
        -- bootstrap the program on main Edh thread
        atomically $ writeTBQueue mainQueue $ EdhDoSTM etsAtBoot $ prog
          etsAtBoot
        -- drive the main Edh thread
        driveEdhThread defers mainQueue

 where

  nextTaskFromQueue :: TBQueue EdhTask -> STM (Maybe EdhTask)
  nextTaskFromQueue = orElse (Nothing <$ readTMVar haltResult) . tryReadTBQueue

  driveDefers :: [DeferRecord] -> IO ()
  driveDefers [] = return ()
  driveDefers ((DeferRecord !etsDefer !deferredProc) : restDefers) = do
    !deferPerceivers <- newTVarIO []
    !deferDefers     <- newTVarIO []
    !deferTaskQueue  <- newTBQueueIO 100
    atomically $ writeTBQueue deferTaskQueue $ EdhDoSTM etsDefer $ deferredProc
      etsDefer { edh'in'tx      = False
               , edh'task'queue = deferTaskQueue
               , edh'perceivers = deferPerceivers
               , edh'defers     = deferDefers
               }
    driveEdhThread deferDefers deferTaskQueue
    driveDefers restDefers

  drivePerceiver :: EdhValue -> PerceiveRecord -> IO Bool
  drivePerceiver !ev (PerceiveRecord _ !etsOrigin !reaction) = do
    !breakThread     <- newTVarIO False
    !reactPerceivers <- newTVarIO []
    !reactDefers     <- newTVarIO []
    !reactTaskQueue  <- newTBQueueIO 100
    let !etsPerceiver = etsOrigin
          { edh'in'tx      = False
          , edh'task'queue = reactTaskQueue
          , edh'perceivers = reactPerceivers
          , edh'defers     = reactDefers
          , edh'context    = (edh'context etsOrigin) { contextMatch = ev }
          }
    atomically $ writeTBQueue reactTaskQueue $ EdhDoSTM etsPerceiver $ reaction
      etsPerceiver
      breakThread
    driveEdhThread reactDefers reactTaskQueue
    atomically $ readTVar breakThread
  drivePerceivers :: [(EdhValue, PerceiveRecord)] -> IO Bool
  drivePerceivers []               = return False
  drivePerceivers ((ev, r) : rest) = drivePerceiver ev r >>= \case
    True  -> return True
    False -> drivePerceivers rest

  driveEdhThread :: TVar [DeferRecord] -> TBQueue EdhTask -> IO ()
  driveEdhThread !defers !tq = atomically (nextTaskFromQueue tq) >>= \case
    Nothing -> -- this thread is done, run defers lastly
      readTVarIO defers >>= driveDefers
    Just (EdhDoIO !ets !actIO) -> do
      -- during actIO, perceivers won't fire, program termination won't stop
      -- this thread
      catch actIO $ \(e :: SomeException) ->
        atomically $ toEdhError ets e $ \ !exv ->
          writeTBQueue tq $ EdhDoSTM ets $ edhThrow ets exv
      driveEdhThread defers tq -- loop another iteration for the thread
    Just (EdhDoSTM !ets !actSTM) -> do
      let doIt = goSTM ets actSTM >>= \case
            True -> -- terminate this thread, after running defers lastly
              readTVarIO defers >>= driveDefers
            False -> -- loop another iteration for the thread
              driveEdhThread defers tq
      catch doIt $ \(e :: SomeException) ->
        atomically $ toEdhError ets e $ \ !exv ->
          writeTBQueue tq $ EdhDoSTM ets $ edhThrow ets exv
      driveEdhThread defers tq -- loop another iteration for the thread

  goSTM :: EdhThreadState -> STM () -> IO Bool
  goSTM !etsTask !actTask = loopSTM
   where

    loopSTM :: IO Bool
    loopSTM = atomically stmJob >>= \case
      Nothing -> return True -- to terminate as program halted
      Just (Right ()) ->
        -- no perceiver has fired, the tx job has already been executed
        return False
      Just (Left !gotevl) -> drivePerceivers gotevl >>= \case
        True -> -- a perceiver is terminating this thread
          return True
        False ->
          -- there've been one or more perceivers fired, the tx job have
          -- been skipped, as no perceiver is terminating the thread,
          -- continue with this tx job
          loopSTM

    -- this is the STM work package, where perceivers can preempt the inline
    -- job on an Edh thread
    stmJob :: STM (Maybe (Either [(EdhValue, PerceiveRecord)] ()))
    stmJob = tryReadTMVar haltResult >>= \case
      Just _ -> return Nothing -- program halted
      Nothing -> -- program still running
        (readTVar (edh'perceivers etsTask) >>= perceiverChk []) >>= \gotevl ->
          if null gotevl
            then -- no perceiver fires, execute the tx job
                 Just . Right <$> actTask
            else -- skip the tx job if at least one perceiver fires
                 return $ Just $ Left gotevl

    perceiverChk
      :: [(EdhValue, PerceiveRecord)]
      -> [PerceiveRecord]
      -> STM [(EdhValue, PerceiveRecord)]
    perceiverChk !gotevl [] = return gotevl
    perceiverChk !gotevl (r@(PerceiveRecord !evc _ _) : rest) =
      tryReadTChan evc >>= \case
        Just !ev -> perceiverChk ((ev, r) : gotevl) rest
        Nothing  -> perceiverChk gotevl rest
