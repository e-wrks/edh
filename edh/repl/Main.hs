
module Main where

import           Prelude
-- import           Debug.Trace

import           Control.Exception
import           Control.Concurrent
import           Control.Concurrent.STM

import           System.Console.Haskeline       ( runInputT
                                                , Settings(..)
                                                , outputStrLn
                                                )

import           Language.Edh.EHI

import           Repl


inputSettings :: Settings IO
inputSettings = Settings { complete       = \(_left, _right) -> return ("", [])
                         , historyFile    = Nothing
                         , autoAddHistory = True
                         }


main :: IO ()
main = do

  mainThId <- myThreadId

  ioChan   <- newEmptyTMVarIO
  runtime  <- defaultEdhRuntime ioChan

  world    <- createEdhWorld runtime
  installEdhBatteries world

  forkFinally (runEdhModule' world "repl") $ \case
    Left  (e :: SomeException) -> throwTo mainThId e
    Right _                    -> atomically $ putTMVar ioChan Nothing

  runInputT inputSettings $ do

    outputStrLn ">> Bare Đ (Edh) Interpreter <<"
    outputStrLn
      "* Blank Screen Syndrome ? Take the Tour as your companion, checkout:"
    outputStrLn "  https://github.com/e-wrks/edh/tree/master/Tour"

    ioLoop ioChan

  flushRuntimeLogs runtime
