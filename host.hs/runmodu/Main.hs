module Main where

-- import           Debug.Trace

import Language.Edh.MHI
import Language.Edh.Run
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn, stderr)
import Prelude

main :: IO ()
main =
  getArgs >>= \case
    [moduSpec] -> edhRunModule defaultEdhConsoleSettings moduSpec $
      \ !world -> do
        -- install all necessary batteries
        installEdhBatteries world

    --
    _ -> hPutStrLn stderr "Usage: edhm <edh-module>" >> exitFailure
