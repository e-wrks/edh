
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

import           Repl


main :: IO ()
main = getArgs >>= \case
  []        -> runModu "repl"
  [edhModu] -> runModu edhModu
  _         -> hPutStrLn stderr "Usage: edh [ <.edh-file> ]" >> exitFailure
 where
  runModu :: FilePath -> IO ()
  runModu !moduSpec = do
    !console <- defaultEdhConsole defaultEdhConsoleSettings
    let !consoleOut = writeTBQueue (consoleIO console) . ConsoleOut

    void $ forkFinally (edhProgLoop moduSpec console) $ \ !result -> do
      case result of
        Left (e :: SomeException) ->
          atomically $ consoleOut $ "💥 " <> T.pack (show e)
        Right _ -> pure ()
      -- shutdown console IO anyway
      atomically $ writeTBQueue (consoleIO console) ConsoleShutdown

    atomically $ do
      consoleOut ">> Bare Đ (Edh) Interpreter <<\n"
      consoleOut
        "* Blank Screen Syndrome ? Take the Tour as your companion, checkout:\n"
      consoleOut "  https://github.com/e-wrks/edh/tree/master/Tour\n"

    consoleIOLoop console
