{-# LANGUAGE ImplicitParams #-}

module Language.Edh.RuntimeM
  ( createEdhWorld,
    declareEdhOperators,
    installModuleM_,
    installModuleM,
    runProgramM,
    runProgramM_,
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
import Control.Monad.IO.Class
import qualified Data.ByteString as B
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

runProgramM :: EdhWorld -> Edh EdhValue -> IO (Either EdhError EdhValue)
runProgramM !world !prog =
  tryJust edhKnownError $ runProgramM' world prog

runProgramM_ :: EdhWorld -> Edh a -> IO ()
runProgramM_ !world !prog =
  void $
    runProgramM' world $ do
      void prog
      return nil

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

runModuleM :: FilePath -> Edh EdhValue
runModuleM !impPath = runModuleM' impPath $ pure ()

runModuleM' :: FilePath -> Edh () -> Edh EdhValue
runModuleM' !impPath !preRun = do
  !world <- edh'prog'world <$> edhProgramState
  (modu, moduFile, moduSource) <-
    liftIO $ let ?fileExt = ".edh" in prepareModu world
  !moduCtx <- inlineSTM $ moduleContext world modu
  inContext moduCtx $ do
    preRun
    evalSrcM moduFile moduSource
  where
    prepareModu :: (?fileExt :: FilePath) => EdhWorld -> IO (Object, Text, Text)
    prepareModu !world =
      locateEdhMainModule impPath >>= \case
        Left !err ->
          throwHostIO PackageError err
        Right !moduFile -> do
          !fileContent <- B.readFile moduFile
          case streamDecodeUtf8With lenientDecode fileContent of
            Some !moduSource _ _ ->
              (,T.pack moduFile,moduSource)
                <$> createEdhModule world (T.pack impPath) moduFile

installModuleM_ :: Text -> Edh () -> Edh ()
installModuleM_ !moduName !preInstall =
  void $ installModuleM moduName preInstall

installModuleM :: Text -> Edh () -> Edh Object
installModuleM !moduName !preInstall = do
  !world <- edh'prog'world <$> edhProgramState
  !modu <-
    liftIO $
      createEdhModule world moduName $
        T.unpack $ "<host:" <> moduName <> ">"

  !moduCtx <- inlineSTM $ moduleContext world modu
  inContext moduCtx preInstall

  liftSTM $ do
    !moduSlot <- newTVar $ ModuLoaded modu
    !moduMap <- takeTMVar (edh'world'modules world)
    putTMVar (edh'world'modules world) $
      Map.insert (HostModule moduName) moduSlot moduMap

  return modu
