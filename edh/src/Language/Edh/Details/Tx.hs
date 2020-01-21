
module Language.Edh.Details.Tx where

import           Prelude
import           Debug.Trace

import           Control.Exception
import           Control.Monad
import           Control.Monad.Reader

import           Control.Concurrent
import           Control.Concurrent.STM

import qualified Data.Map.Strict               as Map

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate


-- | Edh follows GHC's program termination criteria that the main thread
-- decides all. see:
--   https://hackage.haskell.org/package/base/docs/Control-Concurrent.html
driveEdhProgram :: Context -> EdhProg (STM ()) -> IO ()
driveEdhProgram !progCtx !prog = do
  -- check async exception mask state
  getMaskingState >>= \case
    Unmasked -> return ()
    _        -> throwIO
      $ UsageError "Edh program should not run with async exceptions masked"

  -- prepare program environment
  !mainThId <- myThreadId
  let onDescendantExc :: SomeException -> IO ()
      onDescendantExc e = case asyncExceptionFromException e of
        Just (asyncExc :: SomeAsyncException) ->
          -- todo special handling here ?
          throwTo mainThId asyncExc
        _ -> throwTo mainThId e
  !(progHaltSig :: TChan ()      ) <- newBroadcastTChanIO
  !(forkQueue :: TQueue EdhTxTask) <- newTQueueIO
  let
    forkDescendants :: TChan () -> IO ()
    forkDescendants haltSig =
      atomically
          (        (Nothing <$ readTChan haltSig)
          `orElse` (Just <$> readTQueue forkQueue)
          )
        >>= \case
              Nothing -> -- program halted, done
                return ()
              Just (EdhTxTask !pgsFork _ !input !task) -> do
                -- got one to fork, prepare state for the descendant thread
                !(descQueue :: TQueue EdhTxTask) <- newTQueueIO
                !(descHaltSig :: TChan ()) <- atomically $ dupTChan progHaltSig
                !reactors                        <- newTVarIO []
                !defers                          <- newTVarIO []
                let !pgsDescendant = pgsFork { edh'task'queue = descQueue
                                             , edh'reactors   = reactors
                                             , edh'defers     = defers
                    -- the forker should have checked not in tx, enforce here
                                             , edh'in'tx      = False
                                             }
                    !descTaskSource = (Nothing <$ readTChan descHaltSig)
                      `orElse` tryReadTQueue descQueue
                -- bootstrap on the descendant thread
                atomically $ writeTQueue
                  descQueue
                  (EdhTxTask pgsDescendant False input task)
                void
                  $ mask_
                  $ forkIOWithUnmask
                  $ \unmask -> catch
                      (unmask $ driveEdhThread defers descTaskSource)
                      onDescendantExc
                -- loop another iteration
                forkDescendants haltSig
  -- start forker thread
  forkerHaltSig <- -- forker's sig reader chan must be dup'ed from the broadcast
    -- chan by the main thread, if by the forker thread, it can omit the signal
    -- thus block indefinitely, bcoz racing with main thread's finish
                   atomically $ dupTChan progHaltSig
  void $ mask_ $ forkIOWithUnmask $ \unmask ->
    catch (unmask $ forkDescendants forkerHaltSig) onDescendantExc
  -- broadcast the halt signal after the main thread done anyway
  flip finally (atomically $ writeTChan progHaltSig ()) $ do
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
    driveEdhThread defers $ tryReadTQueue mainQueue

 where

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
    driveEdhThread deferDefers (tryReadTQueue deferTaskQueue)
    driveDefers restDefers

  driveReactor :: EdhValue -> ReactorRecord -> IO Bool
  driveReactor !ev (_, pgsOrigin, argsRcvr, stmt) = do
    !breakThread <- newEmptyTMVarIO
    let
      !ctxReactor = edh'context pgsOrigin
      !apk        = case ev of
        EdhArgsPack apk_ -> apk_
        _                -> ArgsPack [ev] Map.empty
      !scopeAtReactor = contextScope ctxReactor
      !reactorProg    = ask >>= \pgsReactor ->
        recvEdhArgs ctxReactor argsRcvr apk $ \ent -> contEdhSTM $ do
          em <- readTVar ent
          modifyTVar' (scopeEntity scopeAtReactor) $ Map.union em
          runEdhProg pgsReactor
            $ evalStmt stmt
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
    driveEdhThread reactDefers (tryReadTQueue reactTaskQueue)
    atomically $ readTMVar breakThread
  driveReactors :: [(EdhValue, ReactorRecord)] -> IO Bool
  driveReactors []               = return False
  driveReactors ((ev, r) : rest) = driveReactor ev r >>= \case
    True  -> return True
    False -> driveReactors rest

  driveEdhThread :: TVar [DeferRecord] -> STM (Maybe EdhTxTask) -> IO ()
  driveEdhThread !defers !taskSource = atomically taskSource >>= \case
    Nothing -> -- this thread is done, run defers lastly
      readTVarIO defers >>= driveDefers
    Just txTask -> goSTM 0 txTask >>= \case -- run this task
      True -> -- terminate this thread, after running defers lastly
        readTVarIO defers >>= driveDefers
      False -> -- loop another iteration for the thread
        driveEdhThread defers taskSource

  goSTM :: Int -> EdhTxTask -> IO Bool
  goSTM !rtc (EdhTxTask !pgsThread !wait !input !task) = if wait
    then -- let stm do the retry, for blocking read of a 'TChan' etc.
         waitSTM
    else -- blocking wait not expected, track stm retries explicitly
         doSTM rtc

   where

    waitSTM :: IO Bool
    waitSTM = atomically stmJob >>= \case
      [] -> -- no reactor fires, the tx job has been executed
        return False
      gotevl -> driveReactors gotevl >>= \case
        True -> -- a reactor is terminating this thread
          return True
        False ->
          -- there've been one or more reactors fired, the tx job have
          -- been skipped, as no reactor is terminating the thread,
          -- continue with this tx job
          waitSTM

    doSTM :: Int -> IO Bool
    doSTM !rtc' = do

      when -- todo increase the threshold of reporting?
           (rtc' > 0) $ do
        -- trace out the retries so the end users can be aware of them
        tid <- myThreadId
        trace (" 🌀 " <> show tid <> " stm retry #" <> show rtc') $ return ()

      atomically ((Just <$> stmJob) `orElse` return Nothing) >>= \case
        Nothing -> -- ^ stm failed, do a tracked retry
          doSTM (rtc' + 1)
        Just [] ->
          -- no reactor has fired, the tx job has already been executed
          return False
        Just !gotevl -> driveReactors gotevl >>= \case
          True -> -- a reactor is terminating this thread
            return True
          False ->
            -- there've been one or more reactors fired, the tx job have
            -- been skipped, as no reactor is terminating the thread,
            -- continue with this tx job
            doSTM rtc'

    stmJob :: STM [(EdhValue, ReactorRecord)]
    stmJob =
      (readTVar (edh'reactors pgsThread) >>= reactorChk []) >>= \gotevl ->
        if null gotevl
          then -- no reactor fires, execute the tx job
               join (runReaderT (task input) pgsThread) >> return []
          else -- skip the tx job if at least one reactor fires
               return gotevl

    reactorChk
      :: [(EdhValue, ReactorRecord)]
      -> [ReactorRecord]
      -> STM [(EdhValue, ReactorRecord)]
    reactorChk !gotevl []                        = return gotevl
    reactorChk !gotevl (r@(evc, _, _, _) : rest) = tryReadTChan evc >>= \case
      Just !ev -> reactorChk ((ev, r) : gotevl) rest
      Nothing  -> reactorChk gotevl rest
