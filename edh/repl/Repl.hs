
module Repl where

import           Prelude
-- import           Debug.Trace

import           Text.Printf

import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T

import           System.Console.Haskeline

import           Language.Edh.EHI


-- | The default Edh command prompts
--
-- ps1 is for single line, ps2 for multi-line
-- 
-- note the defaults here are technically in no effect, just advice
-- see implementation of:
--   runtime.readCommands(ps1="Đ: ", ps2="Đ| ")
defaultPS1, defaultPS2 :: Text
defaultPS1 = "Đ: "
defaultPS2 = "Đ| "


-- | Manage lifecycle of Edh programs during the repl session
edhProgLoop :: TQueue EdhConsoleIO -> EdhWorld -> IO ()
edhProgLoop !ioQ !world = loop
 where
  loop = do
    runEdhModule world "repl" >>= \case
      Left  err -> atomically $ writeTQueue ioQ $ ConsoleOut $ T.pack $ show err
      Right ()  -> pure ()
    atomically $ writeTQueue ioQ $ ConsoleOut "🐴🐴🐯🐯"
    loop


-- | Serialize output to `stdout` from Edh programs, and give them command
-- line input when requested
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


-- | The repl line reader
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
