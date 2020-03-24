
module Repl where

import           Prelude
-- import           Debug.Trace

import           Text.Printf

import           Control.Monad

import           Control.Monad.Reader

import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T

import           System.Console.Haskeline

import           Language.Edh.EHI


edhProgLoop :: TQueue EdhConsoleIO -> EdhWorld -> IO ()
edhProgLoop !ioQ !world = loop
 where
  loop = do
    runEdhModule world "repl" >>= \case
      Left  err -> atomically $ writeTQueue ioQ $ ConsoleOut $ T.pack $ show err
      Right ()  -> pure ()
    atomically $ writeTQueue ioQ $ ConsoleOut "🐴🐴🐯🐯"
    loop


ioLoop :: TQueue EdhConsoleIO -> InputT IO ()
ioLoop !ioQ = liftIO (atomically $ readTQueue ioQ) >>= \case
  ConsoleShutdown    -> return () -- gracefully stop the io loop
  ConsoleOut !txtOut -> do
    outputStrLn $ T.unpack txtOut
    ioLoop ioQ
  ConsoleIn !cmdIn !ps1 !ps2 -> readInput ps1 ps2 [] >>= \case
    Nothing -> -- reached EOF (end-of-feed)
      return ()
    Just !cmd -> do -- got one piece of code
      liftIO $ atomically $ putTMVar cmdIn cmd
      ioLoop ioQ


defaultPS1, defaultPS2 :: Text
defaultPS1 = "Đ: "
defaultPS2 = "Đ| "

readInput :: Text -> Text -> [Text] -> InputT IO (Maybe Text)
readInput !ps1 !ps2 !initialLines =
  handleInterrupt ( -- start over on Ctrl^C
                   outputStrLn "" >> readLines [])
    $ withInterrupt
    $ readLines initialLines
 where
  readLines pendingLines = getInputLine prompt >>= \case
    Nothing -> case pendingLines of
      [] -> return Nothing
      _ -> -- TODO warn about premature EOF ?
        return Nothing
    Just text ->
      let code = T.pack text
      in  case pendingLines of
            [] -> case T.stripEnd code of
              "{" -> -- an unindented `{` marks start of multi-line input
                readLines [""]
              _ -> case T.strip code of
                "" -> -- got an empty line in single-line input mode
                  readLines [] -- start over in single-line input mode
                _ -> -- got a single line input
                  return $ Just code
            _ -> case T.stripEnd code of
              "}" -> -- an unindented `}` marks end of multi-line input
                return $ Just $ (T.unlines . reverse) $ init pendingLines
              _ -> -- got a line in multi-line input mode
                readLines $ code : pendingLines
   where
    prompt :: String
    prompt = case pendingLines of
      [] -> T.unpack ps1
      _  -> T.unpack ps2 <> printf "%2d" (length pendingLines) <> ": "
