
module Main where

import           Prelude
-- import           Debug.Trace

import           System.Console.Haskeline

import           Language.Edh.Runtime
import           Language.Edh.Interpreter
import           Language.Edh.Batteries

import           Repl                           ( doLoop )


inputSettings :: Settings IO
inputSettings = Settings { complete       = \(_left, _right) -> return ("", [])
                         , historyFile    = Nothing
                         , autoAddHistory = True
                         }


main :: IO ()
main = do

  -- todo create a logger coop'ing with haskeline specifically ?
  logger <- defaultEdhLogger

  runInputT inputSettings $ do

    outputStrLn ">> Bare Đ (Edh) Interpreter <<"
    outputStrLn
      "* Blank Screen Syndrome ? Take the Tour as your companion, checkout:"
    outputStrLn "  https://github.com/e-wrks/edh/tree/master/Tour"

    world <- createEdhWorld logger
    installEdhBatteries world

    modu <- createEdhModule world "<interactive>" "<adhoc>"
    doLoop world modu

