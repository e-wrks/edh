
module Main where

import           Prelude
-- import           Debug.Trace

import           Control.Monad
import           Control.Exception
import           Control.Concurrent
import           Control.Concurrent.STM

import qualified Data.Text                     as T

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

  ioQ     <- newTQueueIO
  runtime <- defaultEdhRuntime ioQ

  world   <- createEdhWorld runtime
  installEdhBatteries world

  void $ forkFinally (edhProgLoop ioQ world) $ \result -> do
    case result of
      Left (e :: SomeException) ->
        atomically $ writeTQueue ioQ $ ConsoleOut $ "💥 " <> T.pack (show e)
      Right _ -> atomically $ writeTQueue ioQ $ ConsoleOut "Bye."
    atomically $ writeTQueue ioQ ConsoleShutdown

  runInputT inputSettings $ do
    outputStrLn ">> Bare Đ (Edh) Interpreter <<"
    outputStrLn
      "* Blank Screen Syndrome ? Take the Tour as your companion, checkout:"
    outputStrLn "  https://github.com/e-wrks/edh/tree/master/Tour"
    ioLoop ioQ

  flushRuntimeLogs runtime
