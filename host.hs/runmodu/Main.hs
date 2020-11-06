
module Main where

import           Prelude
-- import           Debug.Trace

import           System.Environment
import           System.IO
import           System.Exit

import           Control.Monad
import           Control.Exception
import           Control.Concurrent
import           Control.Concurrent.STM

import qualified Data.Text                     as T

import           Language.Edh.EHI


main :: IO ()
main = getArgs >>= \case
  [moduSpec] -> do

    !console <- defaultEdhConsole defaultEdhConsoleSettings
    let !consoleOut      = writeTBQueue (consoleIO console) . ConsoleOut
        !consoleShutdown = writeTBQueue (consoleIO console) ConsoleShutdown
        consoleErr msg =
          consoleLogger console 50 Nothing $ ArgsPack [EdhString msg] odEmpty
        runIt = do

          world <- createEdhWorld console
          installEdhBatteries world
          runEdhModule world moduSpec edhModuleAsIs >>= \case
            Left !err -> atomically $ do
              -- program crash on error
              consoleErr
                $  T.pack
                $  "Edh crashed with an error:\n"
                <> show err
                <> "\n"
              consoleShutdown
            Right !phv -> case edhUltimate phv of
              -- clean program halt, all done
              EdhNil -> return ()
              -- unclean program exit
              _      -> atomically $ do
                consoleErr
                  $  (<> "\n")
                  $  "Edh halted with a result:\n"
                  <> case phv of
                       EdhString msg -> msg
                       _             -> T.pack $ show phv
                consoleShutdown

    void $ forkFinally runIt $ \ !result -> do
      case result of
        Left (e :: SomeException) ->
          atomically $ consoleOut $ "💥 " <> T.pack (show e)
        Right _ -> pure ()
      -- shutdown console IO anyway
      atomically $ writeTBQueue (consoleIO console) ConsoleShutdown

    consoleIOLoop console

  _ -> hPutStrLn stderr "Usage: edhm <edh-module>" >> exitFailure
