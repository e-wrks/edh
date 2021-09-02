module Language.Edh.Run where

-- import           Debug.Trace

import Control.Concurrent
import Control.Exception
import Control.Monad
import Data.IORef
import qualified Data.Text as T
import Language.Edh.CHI
import System.Clock
import qualified System.Console.Haskeline as Haskeline
import System.IO (hPutStrLn, stderr)
import System.Mem.Weak
import System.Posix.Signals
import Prelude

-- | Run an Edh source file with the specified console settings
edhRunFile :: Haskeline.Settings IO -> FilePath -> (EdhWorld -> IO ()) -> IO ()
edhRunFile !consoleSettings !fileSpec !worldInit = do
  !console <- defaultEdhConsole consoleSettings

  !mainTh <- mkWeakThreadId =<< myThreadId
  !progTh <- (mkWeakThreadId =<<) $
    forkFinally (edhRunFile' console fileSpec worldInit) $ \ !result -> do
      case result of
        Left (e :: SomeException) ->
          hPutStrLn stderr $ "💥 " <> show e
        Right _ -> pure ()
      -- shutdown console IO anyway
      consoleIO console ConsoleShutdown

  !lastIntTime <- newIORef 0
  let interrupt = do
        !lastTime <- readIORef lastIntTime
        !thisTime <- getTime Monotonic
        writeIORef lastIntTime thisTime
        if thisTime - lastTime < TimeSpec 1 0
          then -- double Ctrl^C, quit the process by killing main thread

            deRefWeak mainTh >>= \case
              Just !thMain -> killThread thMain
              Nothing -> pure () -- already dead, but is this reachable?
          else -- single Ctrl^C, send interrupt to the main thread

            deRefWeak mainTh >>= \case
              Just !thMain -> throwTo thMain UserInterrupt
              Nothing -> pure () -- already dead, but is this reachable?
  _ <- installHandler sigINT (Catch interrupt) Nothing

  let keepIO = catch (consoleIOLoop console) $ \case
        UserInterrupt -> do
          -- propagated to here, the prog was not blocked by console read,
          -- let's send cancellation to the prog thread, whatever it's doing
          deRefWeak progTh >>= \case
            Just !thRunFile -> throwTo thRunFile UserInterrupt
            Nothing -> pure () -- the console IO loop should "finally"
            -- shutdown once the prog thread terminates, do nothing here
          keepIO
        ThreadKilled ->
          -- usual quit in responding to double Ctrl^C
          hPutStrLn stderr "Unclean quit as you double-pressed Ctrl^C, sorry.\n"
        ex -> throwIO ex
  keepIO

-- | Run an Edh source file with the specified console setup
edhRunFile' :: EdhConsole -> FilePath -> (EdhWorld -> IO ()) -> IO ()
edhRunFile' !console !fileSpec !worldInit = do
  !world <- createEdhWorld console
  worldInit world

  runEdhFile world fileSpec >>= \case
    Left !err -> do
      -- program crash on error
      hPutStrLn stderr "Edh program crashed with an error:\n"
      hPutStrLn stderr $ show err <> "\n"
    Right !phv -> case edhUltimate phv of
      -- clean program halt, all done
      EdhNil -> return ()
      -- unclean program exit
      _ -> do
        hPutStrLn stderr "Edh program halted with a result:\n"
        hPutStrLn stderr $
          (<> "\n") $ case phv of
            EdhString msg -> T.unpack msg
            _ -> show phv

-- | Run an Edh module with the specified console settings
edhRunModule :: Haskeline.Settings IO -> FilePath -> (EdhWorld -> IO ()) -> IO ()
edhRunModule !consoleSettings !moduSpec !worldInit = do
  !console <- defaultEdhConsole consoleSettings

  !mainTh <- mkWeakThreadId =<< myThreadId
  !progTh <- (mkWeakThreadId =<<) $
    forkFinally (edhRunModule' console moduSpec worldInit) $ \ !result -> do
      case result of
        Left (e :: SomeException) ->
          hPutStrLn stderr $ "💥 " <> show e
        Right _ -> pure ()
      -- shutdown console IO anyway
      consoleIO console ConsoleShutdown

  !lastIntTime <- newIORef 0
  let interrupt = do
        !lastTime <- readIORef lastIntTime
        !thisTime <- getTime Monotonic
        writeIORef lastIntTime thisTime
        if thisTime - lastTime < TimeSpec 1 0
          then -- double Ctrl^C, quit the process by killing main thread

            deRefWeak mainTh >>= \case
              Just !thMain -> killThread thMain
              Nothing -> pure () -- already dead, but is this reachable?
          else -- single Ctrl^C, send interrupt to the main thread

            deRefWeak mainTh >>= \case
              Just !thMain -> throwTo thMain UserInterrupt
              Nothing -> pure () -- already dead, but is this reachable?
  _ <- installHandler sigINT (Catch interrupt) Nothing

  let keepIO = catch (consoleIOLoop console) $ \case
        UserInterrupt -> do
          -- propagated to here, the prog was not blocked by console read,
          -- let's send cancellation to the prog thread, whatever it's doing
          deRefWeak progTh >>= \case
            Just !thRunModu -> throwTo thRunModu UserInterrupt
            Nothing -> pure () -- the console IO loop should "finally"
            -- shutdown once the prog thread terminates, do nothing here
          keepIO
        ThreadKilled ->
          -- usual quit in responding to double Ctrl^C
          hPutStrLn stderr "Unclean quit as you double-pressed Ctrl^C, sorry.\n"
        ex -> throwIO ex
  keepIO

-- | Run an Edh module with the specified console setup
edhRunModule' :: EdhConsole -> FilePath -> (EdhWorld -> IO ()) -> IO ()
edhRunModule' !console !moduSpec !worldInit = do
  !world <- createEdhWorld console
  worldInit world

  runEdhModule world moduSpec edhModuleAsIs >>= \case
    Left !err -> do
      -- program crash on error
      hPutStrLn stderr "Edh program crashed with an error:\n"
      hPutStrLn stderr $ show err <> "\n"
    Right !phv -> case edhUltimate phv of
      -- clean program halt, all done
      EdhNil -> return ()
      -- unclean program exit
      _ -> do
        hPutStrLn stderr "Edh program halted with a result:\n"
        hPutStrLn stderr $
          (<> "\n") $ case phv of
            EdhString msg -> T.unpack msg
            _ -> show phv
