{-# LANGUAGE ImplicitParams #-}

-- | Edh package management functionalities
module Language.Edh.PkgMan where

-- import Debug.Trace

import Data.Text (Text)
import qualified Data.Text as T
import Language.Edh.Control
import System.Directory
import System.FilePath
import Prelude

locateEdhFile ::
  (?frontFile :: FilePath, ?fileExt :: FilePath) =>
  Text ->
  FilePath ->
  IO (Either Text (ModuleName, FilePath))
locateEdhFile !nomSpec !baseDir =
  doesPathExist baseDir >>= \case
    False ->
      return $ Left $ "path does not exist: " <> T.pack baseDir
    True ->
      fmap pathToName
        <$> if "." `T.isPrefixOf` nomSpec
          then resolveRelativeImport nomSpec baseDir
          else resolveAbsoluteImport nomSpec "."
  where
    pathToName :: (FilePath, FilePath) -> (ModuleName, FilePath)
    pathToName (!nomPath, !filePath) =
      let (_homePath, !moduName) =
            T.breakOnEnd "/edh_modules/" $ T.pack nomPath
       in (moduName, filePath)

resolveRelativeImport ::
  (?frontFile :: FilePath, ?fileExt :: FilePath) =>
  Text ->
  FilePath ->
  IO (Either Text (FilePath, FilePath))
resolveRelativeImport !nomSpec !baseDir = do
  !canoDir <- canonicalizePath baseDir
  !nomPath <- canonicalizePath $ canoDir </> T.unpack nomSpec
  let !edhFrontPath = nomPath </> ?frontFile
   in doesFileExist edhFrontPath >>= \case
        True -> return $ Right (nomPath, edhFrontPath)
        False -> do
          let !edhFilePath = nomPath <> ?fileExt
          doesFileExist edhFilePath >>= \case
            True -> return $ Right (nomPath, edhFilePath)
            False ->
              return $
                Left $
                  T.pack $
                    "no such Edh "
                      <> ?fileExt
                      <> " file: "
                      <> T.unpack nomSpec
                      <> " relative to: "
                      <> canoDir

resolveAbsoluteImport ::
  (?frontFile :: FilePath, ?fileExt :: FilePath) =>
  Text ->
  FilePath ->
  IO (Either Text (FilePath, FilePath))
resolveAbsoluteImport !nomSpec !baseDir = canonicalizePath baseDir >>= go
  where
    !moduSpec = T.unpack nomSpec
    go !absPkgPath =
      let !emsDir = absPkgPath </> "edh_modules"
       in doesDirectoryExist emsDir >>= \case
            False -> tryParentDir
            True -> do
              !nomPath <- canonicalizePath $ emsDir </> moduSpec
              let !edhFrontPath = nomPath </> ?frontFile
              doesFileExist edhFrontPath >>= \case
                True ->
                  return $ Right (nomPath, edhFrontPath)
                False -> do
                  let !edhFilePath = nomPath <> ?fileExt
                  doesFileExist edhFilePath >>= \case
                    True ->
                      return $ Right (nomPath, edhFilePath)
                    False ->
                      tryParentDir
      where
        tryParentDir =
          let !parentPkgPath = takeDirectory absPkgPath
           in if equalFilePath parentPkgPath absPkgPath
                then
                  return $
                    Left $
                      T.pack
                        ("no such Edh " <> ?fileExt <> " file: ")
                        <> nomSpec
                        <> " around "
                        <> T.pack baseDir
                else go parentPkgPath

locateEdhMainModule ::
  (?fileExt :: FilePath) => FilePath -> IO (Either Text FilePath)
locateEdhMainModule !importPath = do
  !cwd <- canonicalizePath "."
  let resolveMainImport :: FilePath -> IO (Either Text FilePath)
      resolveMainImport !absPkgPath = do
        let !nomPath = absPkgPath </> "edh_modules" </> importPath
            !edhFilePath = nomPath </> ("__main__" <> ?fileExt)
        doesFileExist edhFilePath >>= \case
          True -> return $ Right edhFilePath
          False -> do
            let !parentPkgPath = takeDirectory absPkgPath
            if equalFilePath parentPkgPath absPkgPath
              then
                return $
                  Left $
                    T.pack $
                      "no such main module: ["
                        <> importPath
                        <> "] from ["
                        <> cwd
                        <> "]"
              else resolveMainImport parentPkgPath
  resolveMainImport cwd
