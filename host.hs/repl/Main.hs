module Main where

-- import           Debug.Trace

import Control.Concurrent (forkFinally)
import Control.Exception (SomeException)
import Control.Monad (void)
import qualified Data.Text as T
import Language.Edh.EHI
  ( EdhConsole (consoleIO, consoleIOLoop),
    EdhConsoleIO (ConsoleOut, ConsoleShutdown),
    defaultEdhConsole,
    defaultEdhConsoleSettings,
  )
import Repl (edhProgLoop)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Prelude

main :: IO ()
main =
  getArgs >>= \case
    [] -> runModu "repl"
    [edhModu] -> runModu edhModu
    _ -> hPutStrLn stderr "Usage: edh [ <edh-module> ]" >> exitFailure
  where
    runModu :: FilePath -> IO ()
    runModu !moduSpec = do
      !console <- defaultEdhConsole defaultEdhConsoleSettings
      let !consoleOut =  (consoleIO console) . ConsoleOut

      void $
        forkFinally (edhProgLoop moduSpec console) $ \ !result -> do
          case result of
            Left (e :: SomeException) ->
              consoleOut $ "💥 " <> T.pack (show e)
            Right _ -> pure ()
          -- shutdown console IO anyway
          consoleIO console ConsoleShutdown

      consoleOut ">> Bare Đ (Edh) Interpreter <<\n"
      consoleOut
        "* Blank Screen Syndrome ? Take the Tour as your companion, checkout:\n"
      consoleOut "  https://github.com/e-wrks/edh/tree/master/Tour\n"

      consoleIOLoop console
