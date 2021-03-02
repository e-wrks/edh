module Main where

-- import           Debug.Trace

import Control.Concurrent (forkFinally)
import Control.Concurrent.STM
import Control.Exception (SomeException)
import Control.Monad (void)
import qualified Data.Text as T
import Language.Edh.EHI
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Prelude

main :: IO ()
main =
  getArgs >>= \case
    [moduSpec] -> do
      !console <- defaultEdhConsole defaultEdhConsoleSettings
      let !consoleOut = consoleIO console . ConsoleOut
          !consoleShutdown = consoleIO console ConsoleShutdown
          consoleErr msg =
            consoleLogger console 50 Nothing msg
          runIt = do
            world <- createEdhWorld console
            installEdhBatteries world
            runEdhModule world moduSpec edhModuleAsIs >>= \case
              Left !err -> do
                -- program crash on error
                atomically $
                  consoleErr $
                    T.pack $ "Edh crashed with an error:\n" <> show err <> "\n"
                consoleShutdown
              Right !phv -> case edhUltimate phv of
                -- clean program halt, all done
                EdhNil -> return ()
                -- unclean program exit
                _ -> do
                  atomically $
                    consoleErr $
                      (<> "\n") $
                        "Edh halted with a result:\n"
                          <> case phv of
                            EdhString msg -> msg
                            _ -> T.pack $ show phv
                  consoleShutdown

      void $
        forkFinally runIt $ \ !result -> do
          case result of
            Left (e :: SomeException) ->
              consoleOut $ "💥 " <> T.pack (show e)
            Right _ -> pure ()
          -- shutdown console IO anyway
          consoleIO console ConsoleShutdown

      consoleIOLoop console
    _ -> hPutStrLn stderr "Usage: edhm <edh-module>" >> exitFailure
