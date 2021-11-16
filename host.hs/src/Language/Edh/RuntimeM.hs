{-# LANGUAGE ImplicitParams #-}

module Language.Edh.RuntimeM
  ( createEdhWorld,
    declareEdhOperators,
    installModuleM_,
    installModuleM,
    runProgramM,
    runProgramM',
    createEdhModule,
    runModuleM,
    runModuleM',
    runEdhFile,
    runEdhFile',
  )
where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import qualified Data.ByteString as B
import Data.Dynamic
import qualified Data.HashMap.Strict as Map
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding
import Data.Text.Encoding.Error
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.Monad
import Language.Edh.PkgMan
import Language.Edh.RtTypes
import Language.Edh.Runtime
import System.FilePath
import Prelude

installModuleM_ :: EdhWorld -> Text -> Edh () -> IO ()
installModuleM_ !world !moduName !preInstall =
  void $ installModuleM world moduName preInstall

installModuleM :: EdhWorld -> Text -> Edh () -> IO Object
installModuleM !world !moduName !preInstall = do
  !modu <-
    createEdhModule world moduName $ T.unpack $ "<host:" <> moduName <> ">"
  void $
    runProgramM' world $ do
      !moduCtx <- inlineSTM $ moduleContext world modu
      inContext moduCtx preInstall
      inlineSTM $ do
        !moduSlot <- newTVar $ ModuLoaded modu
        !moduMap <- takeTMVar (edh'world'modules world)
        putTMVar (edh'world'modules world) $
          Map.insert (HostModule moduName) moduSlot moduMap
      return nil
  return modu

runProgramM :: EdhWorld -> Edh EdhValue -> IO (Either EdhError EdhValue)
runProgramM !world !prog =
  tryJust edhKnownError $ runProgramM' world prog

runProgramM' :: EdhWorld -> Edh EdhValue -> IO EdhValue
runProgramM' !world !prog = do
  !haltResult <- newEmptyTMVarIO
  let exit :: EdhTxExit EdhValue
      exit val _ets = void $ tryPutTMVar haltResult (Right val)
  driveEdhProgram haltResult world $ \ !ets ->
    unEdh prog rptEdhNotApplicable exit ets
  atomically (tryReadTMVar haltResult) >>= \case
    Nothing -> return nil
    Just (Right v) -> return v
    Just (Left e) -> throwIO e

runModuleM :: EdhWorld -> FilePath -> Edh () -> IO (Either EdhError EdhValue)
runModuleM !world !impPath !preRun =
  tryJust edhKnownError $ runModuleM' world impPath preRun

runModuleM' :: EdhWorld -> FilePath -> Edh () -> IO EdhValue
runModuleM' !world !impPath !preRun =
  let ?fileExt = ".edh"
   in locateEdhMainModule impPath >>= \case
        Left !err ->
          throwIO $ EdhError PackageError err (toDyn nil) "<run-modu>"
        Right !moduFile -> do
          !fileContent <- B.readFile moduFile
          case streamDecodeUtf8With lenientDecode fileContent of
            Some !moduSource _ _ -> do
              !modu <- createEdhModule world (T.pack impPath) moduFile
              runProgramM' world $ do
                !moduCtx <- inlineSTM $ moduleContext world modu
                inContext moduCtx $ do
                  preRun
                  evalSrcM (T.pack moduFile) moduSource
