
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


ioLoop :: TMVar (Maybe (TMVar Text)) -> InputT IO ()
ioLoop !ioChan = liftIO (atomically $ takeTMVar ioChan) >>= \case
  Nothing -> return () -- gracefully stop the io loop
  Just io -> liftIO (atomically $ tryReadTMVar io) >>= \case
    -- a full TMVar means out putting
    Just !txtOut -> outputStrLn $ T.unpack txtOut
    -- an empty TMVar means in taking
    Nothing      -> readInput [] >>= \case
      Nothing -> -- reached EOF (end-of-feed)
        liftIO $ atomically $ putTMVar io ""
      Just !code -> do -- got one piece of code
        liftIO $ atomically $ putTMVar io code
        ioLoop ioChan


readInput :: [Text] -> InputT IO (Maybe Text)
readInput pendingLines =
  handleInterrupt (outputStrLn "" >> readInput [])
    $   withInterrupt
    $   getInputLine
          (case pendingLines of
            [] -> "Đ: "
            _  -> "Đ| " <> printf "%2d" (length pendingLines) <> ": "
          )
    >>= \case
          Nothing -> case pendingLines of
            [] -> return Nothing
            _ -> -- TODO warn about premature EOF ?
              return Nothing
          Just text ->
            let code = T.pack text
            in  case pendingLines of
                  [] -> case T.stripEnd code of
                    "{" -> -- an unindented `{` marks start of multi-line input
                      readInput [""]
                    _ -> case T.strip code of
                      "" -> -- got an empty line in single-line input mode
                        readInput [] -- start over in single-line input mode
                      _ -> -- got a single line input
                        return $ Just code
                  _ -> case T.stripEnd code of
                    "}" -> -- an unindented `}` marks end of multi-line input
                      return $ Just $ (T.unlines . reverse) $ init pendingLines
                    _ -> -- got a line in multi-line input mode
                      readInput $ code : pendingLines

