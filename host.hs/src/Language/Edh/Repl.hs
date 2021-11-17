module Language.Edh.Repl where

-- import           Debug.Trace

import Control.Concurrent
import Control.Exception
import Control.Monad
import Data.IORef
import qualified Data.Text as T
import Language.Edh.EHI
import System.Clock
import qualified System.Console.Haskeline as Haskeline
import System.IO (hPutStrLn, stderr)
import System.Mem.Weak
import System.Posix.Signals
import Prelude

edhRepl :: Haskeline.Settings IO -> (EdhWorld -> IO ()) -> FilePath -> IO ()
edhRepl !consoleSettings !worldInit !moduSpec = do
  !console <- defaultEdhConsole consoleSettings

  !mainTh <- mkWeakThreadId =<< myThreadId
  !replTh <- (mkWeakThreadId =<<) $
    forkFinally (edhRepl' console worldInit moduSpec) $ \ !result -> do
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
          -- propagated to here, the repl was not blocked by console read,
          -- let's send cancellation to the repl thread, whatever it's doing
          deRefWeak replTh >>= \case
            Just !thRepl -> throwTo thRepl UserInterrupt
            Nothing -> pure () -- the console IO loop should "finally"
            -- shutdown once the repl thread terminates, do nothing here
          keepIO
        ThreadKilled ->
          -- usual quit in responding to double Ctrl^C
          hPutStrLn stderr "Unclean quit as you double-pressed Ctrl^C, sorry.\n"
        ex -> throwIO ex
  keepIO

-- | Manage lifecycle of Edh programs during the interactive session
edhRepl' :: EdhConsole -> (EdhWorld -> IO ()) -> FilePath -> IO ()
edhRepl' !console !worldInit !moduSpec = do
  -- create the world, we always work with this world no matter how
  -- many times the Edh programs crash
  !world <- createEdhWorld console
  worldInit world

  -- here being the host interpreter, we loop infinite runs of the Edh
  -- console REPL program, unless cleanly shutdown, for resilience
  let doneRightOrRebirth =
        runProgramM world (runModuleM moduSpec) >>= \case
          -- to run a module is to seek its `__main__.edh` and execute the
          -- code there in a volatile module context, it can import itself
          -- (i.e. `__init__.edh`) during the run. all imported modules can
          -- survive program crashes.
          Left !err -> do
            -- program crash on error
            consoleOut "Your program crashed with an error:\n"
            consoleOut $ T.pack $ show err <> "\n"
            -- the world with all modules ever imported, is still
            -- there, repeat another interactive session with this world.
            -- it may not be a good idea, but just so so ...
            consoleOut "🐴🐴🐯🐯 rebirth in 5 seconds...\n"
            threadDelay 5000000
            doneRightOrRebirth
          Right !phv -> case edhUltimate phv of
            EdhNil -> do
              -- clean program halt, all done
              consoleOut "Well done, bye.\n"
              consoleShutdown
            _ -> do
              -- unclean program exit
              consoleOut "Your program halted with a result:\n"
              consoleOut $
                (<> "\n") $ case phv of
                  EdhString msg -> msg
                  _ -> T.pack $ show phv
              -- the world with all modules ever imported, is still
              -- there, repeat another interactive session with this world.
              -- it may not be a good idea, but just so so ...
              consoleOut "🐴🐴🐯🐯 rebirth in 5 seconds...\n"
              threadDelay 5000000
              doneRightOrRebirth
  doneRightOrRebirth
  where
    !consoleOut = consoleIO console . ConsoleOut
    !consoleShutdown = consoleIO console ConsoleShutdown
