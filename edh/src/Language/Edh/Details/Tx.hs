
module Language.Edh.Details.Tx where

import           Prelude
import           Debug.Trace

import           Control.Exception
import           Control.Monad
import           Control.Monad.Reader

import           Control.Concurrent
import           Control.Concurrent.STM

import qualified Data.HashMap.Strict           as Map

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | Edh follows GHC's program termination criteria that the main thread
-- decides all. see:
--   https://hackage.haskell.org/package/base/docs/Control-Concurrent.html
-- description at:
--   https://github.com/e-wrks/edh/tree/master/Tour#program--threading-model
driveEdhProgram
  :: TMVar (Either SomeException EdhValue) -> Context -> EdhProg -> IO ()
driveEdhProgram !haltResult !progCtx !prog = do
  -- check async exception mask state
  getMaskingState >>= \case
    Unmasked -> return ()
    _ ->
      throwIO
        $ UsageError "Edh program should not run with async exceptions masked"
        $ EdhCallContext "<edh>" []

  -- prepare program environment
  !mainThId <- myThreadId
  let onDescendantExc :: SomeException -> IO ()
      onDescendantExc e = case asyncExceptionFromException e of
        Just (asyncExc :: SomeAsyncException) ->
          -- todo special handling here ?
          throwTo mainThId asyncExc
        _ -> throwTo mainThId e
  !(forkQueue :: TQueue (Either (IO ()) EdhTxTask)) <- newTQueueIO
  let
    forkDescendants :: IO ()
    forkDescendants =
      atomically
          (        (Nothing <$ readTMVar haltResult)
          `orElse` (Just <$> readTQueue forkQueue)
          )
        >>= \case
              Nothing        -> return () -- Edh program halted, done
              Just !asyncJob -> do
                case asyncJob of
                  -- got an async IO task to fork
                  Left !ioAct -> void $ mask_ $ forkIOWithUnmask $ \unmask ->
                    catch (unmask ioAct) onDescendantExc
                  -- got an Edh go routine to fork
                  Right !edhTask -> do
                    -- prepare state for the descendant thread
                    !(descQueue :: TQueue EdhTxTask) <- newTQueueIO
                    !reactors                        <- newTVarIO []
                    !defers                          <- newTVarIO []
                    let !pgsDescendant = (edh'task'pgs edhTask)
                          { edh'task'queue = descQueue
                          , edh'reactors   = reactors
                          , edh'defers     = defers
                        -- the forker should have checked not in tx, enforce here
                          , edh'in'tx      = False
                          }
                    -- bootstrap on the descendant thread
                    atomically $ writeTQueue
                      descQueue
                      edhTask { edh'task'pgs = pgsDescendant }
                    void
                      $ mask_
                      $ forkIOWithUnmask
                      $ \unmask -> catch
                          (unmask $ driveEdhThread defers descQueue)
                          onDescendantExc
                -- keep the forker running
                forkDescendants
  -- start forker thread
  void $ mask_ $ forkIOWithUnmask $ \unmask ->
    catch (unmask forkDescendants) onDescendantExc
  -- set halt result after the main thread done, anyway if not already, so all
  -- descendant threads will terminate. 
  -- hanging STM jobs may cause the whole process killed by GHC deadlock detector.
  flip finally (atomically $ void $ tryPutTMVar haltResult (Right nil))
    $ handle
        (\(e :: SomeException) -> do
          atomically $ void $ tryPutTMVar haltResult (Left e)
          throwIO e
        )
    $ do
    -- prepare program state for main thread
        !(mainQueue :: TQueue EdhTxTask) <- newTQueueIO
        !reactors                        <- newTVarIO []
        !defers                          <- newTVarIO []
        let !pgsAtBoot = EdhProgState { edh'fork'queue = forkQueue
                                      , edh'task'queue = mainQueue
                                      , edh'reactors   = reactors
                                      , edh'defers     = defers
                                      , edh'in'tx      = False
                                      , edh'context    = progCtx
                                      }
        -- bootstrap the program on main thread
        atomically $ writeTQueue
          mainQueue
          (EdhTxTask pgsAtBoot False (wuji pgsAtBoot) (const prog))
        -- drive the program from main thread
        driveEdhThread defers mainQueue

 where

  nextTaskFromQueue :: TQueue EdhTxTask -> STM (Maybe EdhTxTask)
  nextTaskFromQueue = orElse (Nothing <$ readTMVar haltResult) . tryReadTQueue

  driveDefers :: [DeferRecord] -> IO ()
  driveDefers [] = return ()
  driveDefers ((!pgsDefer, !deferedProg) : restDefers) = do
    !deferReactors                        <- newTVarIO []
    !deferDefers                          <- newTVarIO []
    !(deferTaskQueue :: TQueue EdhTxTask) <- newTQueueIO
    atomically $ writeTQueue
      deferTaskQueue
      (EdhTxTask
        pgsDefer { edh'task'queue = deferTaskQueue
                 , edh'reactors   = deferReactors
                 , edh'defers     = deferDefers
                 , edh'in'tx      = False
                 }
        False
        (wuji pgsDefer)
        (const deferedProg)
      )
    driveEdhThread deferDefers deferTaskQueue
    driveDefers restDefers

  driveReactor :: EdhValue -> ReactorRecord -> IO Bool
  driveReactor !ev (_, pgsOrigin, argsRcvr, expr) = do
    !breakThread <- newEmptyTMVarIO
    let
      !ctxReactor = edh'context pgsOrigin
      !apk        = case ev of
        EdhArgsPack apk_ -> apk_
        _                -> ArgsPack [ev] Map.empty
      !scopeAtReactor = contextScope ctxReactor
      !reactorProg    = ask >>= \pgsReactor ->
        recvEdhArgs ctxReactor argsRcvr apk $ \em -> contEdhSTM $ do
          updateEntityAttrs pgsReactor (scopeEntity scopeAtReactor)
            $ Map.toList em
          runEdhProg pgsReactor
            $ evalExpr expr
            $ \(OriginalValue !reactorRtn _ _) -> do
                let doBreak = case reactorRtn of
                      EdhBreak -> True -- terminate this thread
                      _        -> False
                contEdhSTM $ putTMVar breakThread doBreak
    !reactReactors                        <- newTVarIO []
    !reactDefers                          <- newTVarIO []
    !(reactTaskQueue :: TQueue EdhTxTask) <- newTQueueIO
    let !pgsReactor = pgsOrigin { edh'task'queue = reactTaskQueue
                                , edh'reactors   = reactReactors
                                , edh'defers     = reactDefers
                                , edh'in'tx      = False
                                }
    atomically $ writeTQueue
      reactTaskQueue
      (EdhTxTask pgsReactor False (wuji pgsReactor) (const reactorProg))
    driveEdhThread reactDefers reactTaskQueue
    atomically $ readTMVar breakThread
  driveReactors :: [(EdhValue, ReactorRecord)] -> IO Bool
  driveReactors []               = return False
  driveReactors ((ev, r) : rest) = driveReactor ev r >>= \case
    True  -> return True
    False -> driveReactors rest

  driveEdhThread :: TVar [DeferRecord] -> TQueue EdhTxTask -> IO ()
  driveEdhThread !defers !tq = atomically (nextTaskFromQueue tq) >>= \case
    Nothing -> -- this thread is done, run defers lastly
      readTVarIO defers >>= driveDefers
    Just txTask -> goSTM txTask >>= \case -- run this task
      True -> -- terminate this thread, after running defers lastly
        readTVarIO defers >>= driveDefers
      False -> -- loop another iteration for the thread
        driveEdhThread defers tq

  goSTM :: EdhTxTask -> IO Bool
  goSTM (EdhTxTask !pgsTask !wait !input !task) = if wait
    then -- let stm do the retry, for blocking read of a 'TChan' etc.
         waitSTM
    else -- blocking wait not expected, track stm retries explicitly
         doSTM 0

   where
    callCtx = getEdhCallContext 0 pgsTask

    waitSTM :: IO Bool
    waitSTM = atomically stmJob >>= \case
      Nothing -> return True -- to terminate as program halted
      Just [] -> -- no reactor fires, the tx job has been executed
        return False
      Just gotevl -> driveReactors gotevl >>= \case
        True -> -- a reactor is terminating this thread
          return True
        False ->
          -- there've been one or more reactors fired, the tx job have
          -- been skipped, as no reactor is terminating the thread,
          -- continue with this tx job
          waitSTM

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
          -- no reactor has fired, the tx job has already been executed
          return False
        Just (Just !gotevl) -> driveReactors gotevl >>= \case
          True -> -- a reactor is terminating this thread
            return True
          False ->
            -- there've been one or more reactors fired, the tx job have
            -- been skipped, as no reactor is terminating the thread,
            -- continue with this tx job
            doSTM rtc

    stmJob :: STM (Maybe [(EdhValue, ReactorRecord)])
    stmJob = tryReadTMVar haltResult >>= \case
      Just _ -> return Nothing -- program halted
      Nothing -> -- program still running
        (readTVar (edh'reactors pgsTask) >>= reactorChk []) >>= \gotevl ->
          if null gotevl
            then -- no reactor fires, execute the tx job
                 join (runReaderT (task input) pgsTask) >> return (Just [])
            else -- skip the tx job if at least one reactor fires
                 return (Just gotevl)

    reactorChk
      :: [(EdhValue, ReactorRecord)]
      -> [ReactorRecord]
      -> STM [(EdhValue, ReactorRecord)]
    reactorChk !gotevl []                        = return gotevl
    reactorChk !gotevl (r@(evc, _, _, _) : rest) = tryReadTChan evc >>= \case
      Just !ev -> reactorChk ((ev, r) : gotevl) rest
      Nothing  -> reactorChk gotevl rest
