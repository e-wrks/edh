
module Language.Edh.Details.Tx where

import           Prelude
import           Debug.Trace

import           Control.Exception
import           Control.Monad
import           Control.Monad.Reader

import           Control.Concurrent
import           Control.Concurrent.STM

import qualified Data.List.NonEmpty            as NE
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
  !forkQueue <- newTQueueIO
  let
    forkDescendants :: IO ()
    forkDescendants =
      atomically
          (        (Nothing <$ readTMVar haltResult)
          `orElse` (Just <$> readTQueue forkQueue)
          )
        >>= \case
              Nothing       -> return () -- Edh program halted, done
              Just !edhTask -> do
                pgsDesc <- deriveState $ edh'task'pgs edhTask
                -- bootstrap on the descendant thread
                atomically
                  $ writeTQueue (edh'task'queue pgsDesc)
                  $ Right edhTask { edh'task'pgs = pgsDesc }
                void $ mask_ $ forkIOWithUnmask $ \unmask -> catch
                  (unmask $ driveEdhThread (edh'defers pgsDesc)
                                           (edh'task'queue pgsDesc)
                  )
                  onDescendantExc
                -- keep the forker running
                forkDescendants
     where
      -- TODO it may be desirable to let exception handlers handle exceptions thrown
      --      from descendant threads ? cases may be investigated for some deal
      -- if the forked go routine doesn't handle an exception itself, treat the
      -- exception as uncaught immediately, it'll be throwTo the main thread then
      handleAsyncExc :: EdhExcptHndlr
      handleAsyncExc !exv _ =
        ask >>= \pgs -> contEdhSTM $ edhErrorUncaught pgs exv
      -- derive program state for the descendant thread
      deriveState :: EdhProgState -> IO EdhProgState
      deriveState !pgsFrom = do
        !descQueue  <- newTQueueIO
        !perceivers <- newTVarIO []
        !defers     <- newTVarIO []
        return pgsFrom
          { edh'task'queue = descQueue
          , edh'perceivers = perceivers
          , edh'defers     = defers
          -- the forker should have checked not in tx, enforce here
          , edh'in'tx      = False
          , edh'context    = fromCtx
            {
              -- disable all exception handlers from parent thread's stack
              callStack        =
              (NE.head fromStack) { exceptionHandler = handleAsyncExc }
                NE.:| NE.tail fromStack
              -- don't be exporting on a forked thread by default
            , contextExporting = False
            }
          }
       where
        !fromCtx   = edh'context pgsFrom
        !fromStack = callStack fromCtx
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
        -- TODO let all live Edh threads go through ProgramHalt propagation,
        --      providing the chance for them to do cleanup.
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
        !mainQueue  <- newTQueueIO
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
        atomically $ writeTQueue mainQueue $ Right
          (EdhTxTask pgsAtBoot (wuji pgsAtBoot) (const prog))
        -- drive the main Edh thread
        driveEdhThread defers mainQueue

 where

  nextTaskFromQueue
    :: TQueue (Either (IO ()) EdhTxTask)
    -> STM (Maybe (Either (IO ()) EdhTxTask))
  nextTaskFromQueue = orElse (Nothing <$ readTMVar haltResult) . tryReadTQueue

  driveDefers :: [DeferRecord] -> IO ()
  driveDefers [] = return ()
  driveDefers ((!pgsDefer, !deferedProg) : restDefers) = do
    !deferPerceivers <- newTVarIO []
    !deferDefers     <- newTVarIO []
    !deferTaskQueue  <- newTQueueIO
    atomically $ writeTQueue deferTaskQueue $ Right $ EdhTxTask
      pgsDefer { edh'task'queue = deferTaskQueue
               , edh'perceivers = deferPerceivers
               , edh'defers     = deferDefers
               , edh'in'tx      = False
               }
      (wuji pgsDefer)
      (const deferedProg)
    driveEdhThread deferDefers deferTaskQueue
    driveDefers restDefers

  drivePerceiver :: EdhValue -> PerceiveRecord -> IO Bool
  drivePerceiver !ev (_, pgsOrigin, reactExpr) = do
    !breakThread <- newEmptyTMVarIO
    let
      !perceiverProg =
        local
            (\pgs ->
              pgs { edh'context = (edh'context pgs) { contextMatch = ev } }
            )
          $ evalMatchingExpr reactExpr
          $ \(OriginalValue !perceiverRtn _ _) -> do
              let doBreak = case perceiverRtn of
                    EdhBreak -> True -- terminate this thread
                    _        -> False
              contEdhSTM $ putTMVar breakThread doBreak
    !reactPerceivers <- newTVarIO []
    !reactDefers     <- newTVarIO []
    !reactTaskQueue  <- newTQueueIO
    let !pgsPerceiver = pgsOrigin { edh'task'queue = reactTaskQueue
                                  , edh'perceivers = reactPerceivers
                                  , edh'defers     = reactDefers
                                  , edh'in'tx      = False
                                  }
    atomically $ writeTQueue reactTaskQueue $ Right $ EdhTxTask
      pgsPerceiver
      (wuji pgsPerceiver)
      (const perceiverProg)
    driveEdhThread reactDefers reactTaskQueue
    atomically $ readTMVar breakThread
  drivePerceivers :: [(EdhValue, PerceiveRecord)] -> IO Bool
  drivePerceivers []               = return False
  drivePerceivers ((ev, r) : rest) = drivePerceiver ev r >>= \case
    True  -> return True
    False -> drivePerceivers rest

  driveEdhThread
    :: TVar [DeferRecord] -> TQueue (Either (IO ()) EdhTxTask) -> IO ()
  driveEdhThread !defers !tq = atomically (nextTaskFromQueue tq) >>= \case
    Nothing -> -- this thread is done, run defers lastly
      readTVarIO defers >>= driveDefers
    Just (Left !ioTask) -> do
      ioTask
      driveEdhThread defers tq -- loop another iteration for the thread
    Just (Right !txTask) -> goSTM txTask >>= \case -- run this task
      True -> -- terminate this thread, after running defers lastly
        readTVarIO defers >>= driveDefers
      False -> -- loop another iteration for the thread
        driveEdhThread defers tq

  -- blocking wait not expected, track stm retries explicitly
  goSTM :: EdhTxTask -> IO Bool
  goSTM (EdhTxTask !pgsTask !input !task) = doSTM 0
   where
    callCtx = getEdhCallContext 0 pgsTask
    doSTM :: Int -> IO Bool
    doSTM !rtc = do

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
        Just Nothing -> return True -- to terminate as program halted
        Nothing -> -- stm failed, do a tracked retry
          doSTM (rtc + 1)
        Just (Just []) ->
          -- no perceiver has fired, the tx job has already been executed
          return False
        Just (Just !gotevl) -> drivePerceivers gotevl >>= \case
          True -> -- a perceiver is terminating this thread
            return True
          False ->
            -- there've been one or more perceivers fired, the tx job have
            -- been skipped, as no perceiver is terminating the thread,
            -- continue with this tx job
            doSTM rtc

    stmJob :: STM (Maybe [(EdhValue, PerceiveRecord)])
    stmJob = tryReadTMVar haltResult >>= \case
      Just _ -> return Nothing -- program halted
      Nothing -> -- program still running
        (readTVar (edh'perceivers pgsTask) >>= perceiverChk []) >>= \gotevl ->
          if null gotevl
            then -- no perceiver fires, execute the tx job
                 join (runReaderT (task input) pgsTask) >> return (Just [])
            else -- skip the tx job if at least one perceiver fires
                 return (Just gotevl)

    perceiverChk
      :: [(EdhValue, PerceiveRecord)]
      -> [PerceiveRecord]
      -> STM [(EdhValue, PerceiveRecord)]
    perceiverChk !gotevl []                     = return gotevl
    perceiverChk !gotevl (r@(evc, _, _) : rest) = tryReadTChan evc >>= \case
      Just !ev -> perceiverChk ((ev, r) : gotevl) rest
      Nothing  -> perceiverChk gotevl rest
