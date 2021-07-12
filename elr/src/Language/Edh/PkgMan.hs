{-# LANGUAGE ImplicitParams #-}

-- | Edh package management functionalities
module Language.Edh.PkgMan where

-- import Debug.Trace

import Data.List (isPrefixOf)
import Data.Text (Text)
import qualified Data.Text as T
import System.Directory
import System.FilePath
import Prelude

edhRelativePathFrom :: FilePath -> FilePath
edhRelativePathFrom !fromPath =
  if "<" `isPrefixOf` fromPath
    then "." -- intrinsic module path
    else takeDirectory fromPath

-- | returns import name, absolute module path and absolute file
--
-- there is a special case of `__init__.edh` for a dir module, where nominal
-- path will point to the directory, otherwise nominal path will be actual file
-- path without `.edh` extension
locateEdhModule ::
  Text ->
  FilePath ->
  IO (Either Text (FilePath, FilePath))
locateEdhModule =
  let ?frontFile = "__init__.edh"
      ?fileExt = ".edh"
   in locateEdhFile

-- | returns include name, absolute fragment path and absolute file
--
-- there is a special case of `__include__.edh` for a dir frag, where nominal
-- path will point to the directory, otherwise nominal path will be actual file
-- path without `.iedh` extension
locateEdhFragment ::
  Text ->
  FilePath ->
  IO (Either Text (FilePath, FilePath))
locateEdhFragment =
  let ?frontFile = "__include__.edh"
      ?fileExt = ".iedh"
   in locateEdhFile

locateEdhFile ::
  (?frontFile :: FilePath, ?fileExt :: FilePath) =>
  Text ->
  FilePath ->
  IO (Either Text (FilePath, FilePath))
locateEdhFile !nomSpec !relPath =
  doesPathExist relPath >>= \case
    False ->
      return $ Left $ "path does not exist: " <> T.pack relPath
    True ->
      if "." `T.isPrefixOf` nomSpec
        then resolveRelativeImport nomSpec relPath
        else resolveAbsoluteImport nomSpec "."

resolveRelativeImport ::
  (?frontFile :: FilePath, ?fileExt :: FilePath) =>
  Text ->
  FilePath ->
  IO (Either Text (FilePath, FilePath))
resolveRelativeImport !nomSpec !relPath = do
  !nomPath <- canonicalizePath $ relPath </> relImp
  let !edhFilePath = nomPath <> ?fileExt
  doesFileExist edhFilePath >>= \case
    True -> return $ Right (nomPath, edhFilePath)
    False ->
      let !edhIdxPath = nomPath </> ?frontFile
       in doesFileExist edhIdxPath >>= \case
            True -> return $ Right (nomPath, edhIdxPath)
            False ->
              return $
                Left $
                  "no such Edh "
                    <> T.pack ?fileExt
                    <> ": "
                    <> T.pack (show relImp)
                    <> " relative to: "
                    <> T.pack relPath
  where
    !relImp = T.unpack nomSpec

resolveAbsoluteImport ::
  (?frontFile :: FilePath, ?fileExt :: FilePath) =>
  Text ->
  FilePath ->
  IO (Either Text (FilePath, FilePath))
resolveAbsoluteImport !nomSpec !pkgPath = canonicalizePath pkgPath >>= go
  where
    !moduSpec = T.unpack nomSpec
    go !absPkgPath =
      let !emsDir = absPkgPath </> "edh_modules"
       in doesDirectoryExist emsDir >>= \case
            False -> tryParentDir
            True -> do
              !nomPath <- canonicalizePath $ emsDir </> moduSpec
              let !edhFilePath = nomPath <> ?fileExt
              doesFileExist edhFilePath >>= \case
                True ->
                  return $ Right (nomPath, edhFilePath)
                False -> do
                  let !edhIdxPath = nomPath </> ?frontFile
                  doesFileExist edhIdxPath >>= \case
                    True ->
                      return $ Right (nomPath, edhIdxPath)
                    False -> tryParentDir
      where
        tryParentDir =
          let !parentPkgPath = takeDirectory absPkgPath
           in if equalFilePath parentPkgPath absPkgPath
                then
                  return $
                    Left $
                      "no such Edh "
                        <> T.pack ?fileExt
                        <> ": "
                        <> T.pack (show nomSpec)
                else go parentPkgPath

locateEdhMainModule :: FilePath -> IO (Either Text (FilePath, FilePath))
locateEdhMainModule !importPath = canonicalizePath "." >>= resolveMainImport
  where
    resolveMainImport :: FilePath -> IO (Either Text (FilePath, FilePath))
    resolveMainImport !absPkgPath = do
      let !nomPath = absPkgPath </> "edh_modules" </> importPath
          !edhFilePath = nomPath </> "__main__.edh"
      doesFileExist edhFilePath >>= \case
        True -> return $ Right (nomPath, edhFilePath)
        False -> do
          let !parentPkgPath = takeDirectory absPkgPath
          if equalFilePath parentPkgPath absPkgPath
            then return $ Left $ "no such main module: " <> T.pack importPath
            else resolveMainImport parentPkgPath
