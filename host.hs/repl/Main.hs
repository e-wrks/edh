module Main where

-- import           Debug.Trace

import Language.Edh.CHI
import Language.Edh.Repl
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Prelude

main :: IO ()
main =
  getArgs >>= \case
    [] -> replWithModule "repl"
    [edhModu] -> replWithModule edhModu
    _ -> hPutStrLn stderr "Usage: edh [ <edh-module> ]" >> exitFailure
  where
    replWithModule :: FilePath -> IO ()
    replWithModule = edhRepl defaultEdhConsoleSettings $ \ !world -> do
      let !consoleOut = consoleIO (edh'world'console world) . ConsoleOut

      -- install all necessary batteries
      installEdhBatteries world

      consoleOut $
        ">> Bare Đ (Edh) Interpreter <<\n"
          <> "* Blank Screen Syndrome ? Take the Tour as your companion, checkout:\n"
          <> "  https://github.com/e-wrks/tour\n"
