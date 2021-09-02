module Main where

-- import           Debug.Trace

import Language.Edh.CHI
import Language.Edh.Run
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Prelude

main :: IO ()
main =
  getArgs >>= \case
    [edhFile] -> edhRunFile defaultEdhConsoleSettings edhFile $ \ !world -> do
      -- install all necessary batteries
      installEdhBatteries world

    --
    _ -> hPutStrLn stderr "Usage: runedh <.edh-file>" >> exitFailure
