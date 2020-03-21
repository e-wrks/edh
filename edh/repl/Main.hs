
module Main where

import           Prelude
-- import           Debug.Trace

import           System.Console.Haskeline

import           Language.Edh.EHI

import           Repl                           ( doLoop )


inputSettings :: Settings IO
inputSettings = Settings { complete       = \(_left, _right) -> return ("", [])
                         , historyFile    = Nothing
                         , autoAddHistory = True
                         }


main :: IO ()
main = do

  -- todo create a runtime with logger coop'ing with haskeline specifically ?
  runtime <- defaultEdhRuntime

  runInputT inputSettings $ do

    outputStrLn ">> Bare Đ (Edh) Interpreter <<"
    outputStrLn
      "* Blank Screen Syndrome ? Take the Tour as your companion, checkout:"
    outputStrLn "  https://github.com/e-wrks/edh/tree/master/Tour"

    world <- createEdhWorld runtime
    installEdhBatteries world

    modu <- createEdhModule world "<interactive>" "<adhoc>"
    doLoop world modu

