
module Repl where

import           Prelude
-- import           Debug.Trace

import           Text.Printf

import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

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
edhProgLoop :: EdhRuntime -> IO ()
edhProgLoop !runtime = do

  -- create the world, we always work with this world no matter how
  -- many times the Edh programs crash
  world <- createEdhWorld runtime
  installEdhBatteries world
  -- install more host modules and/or other artifacts to be available

  -- to run a module is to seek its `__main__.edh` and execute the
  -- code there in a volatile module context, it can import itself
  -- (i.e. `__init__.edh`) during the run. the imported module can
  -- survive program crashes as all imported modules do.
  let loop = runEdhModule world "repl" >>= \case
        Left err -> do -- program crash on error
          atomically $ writeTQueue ioQ $ ConsoleOut $ T.pack $ show err
          -- the world with all modules ever imported, are still there,
          atomically $ writeTQueue ioQ $ ConsoleOut "🐴🐴🐯🐯"
          -- repeat another repl session with this world.
          -- it may not be a good idea, but just so so ...
          loop
        Right phv -> case edhUltimate phv of
          EdhNil -> do -- clean program halt, all done
            atomically $ writeTQueue ioQ $ ConsoleOut
              "Your work committed, bye."
            atomically $ writeTQueue ioQ ConsoleShutdown
          _ -> do -- unclean program exit
            atomically $ writeTQueue ioQ $ ConsoleOut $ case phv of
              EdhString msg -> msg
              _             -> T.pack $ show phv
            -- the world with all modules ever imported, are still there,
            atomically $ writeTQueue ioQ $ ConsoleOut "🐴🐴🐯🐯"
            -- repeat another repl session with this world.
            -- it may not be a good idea, but just so so ...
            loop
  loop
  where ioQ = consoleIO runtime

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
      outputStrLn "Your work may have lost, sorry."
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
