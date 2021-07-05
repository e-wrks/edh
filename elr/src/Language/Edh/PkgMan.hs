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

data ImportName = RelativeName !Text | AbsoluteName !Text

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
  IO (Either Text (ImportName, FilePath, FilePath))
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
  IO (Either Text (ImportName, FilePath, FilePath))
locateEdhFragment =
  let ?frontFile = "__include__.edh"
      ?fileExt = ".iedh"
   in locateEdhFile

locateEdhFile ::
  (?frontFile :: FilePath, ?fileExt :: FilePath) =>
  Text ->
  FilePath ->
  IO (Either Text (ImportName, FilePath, FilePath))
locateEdhFile !nomSpec !relPath =
  doesPathExist relPath >>= \case
    False ->
      return $ Left $ "path does not exist: " <> T.pack relPath
    True ->
      if "." `T.isPrefixOf` nomSpec
        then
          fmap (\(!name, !path, !file) -> (RelativeName name, path, file))
            <$> resolveRelativeImport nomSpec relPath
        else
          fmap (\(!name, !path, !file) -> (AbsoluteName name, path, file))
            <$> resolveAbsoluteImport nomSpec "."

resolveRelativeImport ::
  (?frontFile :: FilePath, ?fileExt :: FilePath) =>
  Text ->
  FilePath ->
  IO (Either Text (Text, FilePath, FilePath))
resolveRelativeImport !nomSpec !relPath = do
  !nomPath <- canonicalizePath $ relPath </> relImp
  let !edhFilePath = nomPath <> ?fileExt
  doesFileExist edhFilePath >>= \case
    True -> return $ Right (nomSpec, edhFilePath, edhFilePath)
    False ->
      let !edhIdxPath = nomPath </> ?frontFile
       in doesFileExist edhIdxPath >>= \case
            True -> return $ Right (nomSpec, nomPath, edhIdxPath)
            False ->
              return $
                Left $
                  "no such module: " <> T.pack (show relImp)
                    <> " relative to: "
                    <> T.pack relPath
  where
    !relImp = T.unpack nomSpec

resolveAbsoluteImport ::
  (?frontFile :: FilePath, ?fileExt :: FilePath) =>
  Text ->
  FilePath ->
  IO (Either Text (Text, FilePath, FilePath))
resolveAbsoluteImport !nomSpec !pkgPath = canonicalizePath pkgPath >>= go
  where
    !moduSpec = T.unpack nomSpec
    go !absPkgPath =
      let !emsDir = absPkgPath </> "edh_modules"
       in doesDirectoryExist emsDir >>= \case
            False -> tryParentDir
            True -> do
              !moduPath <- canonicalizePath $ emsDir </> moduSpec
              let !edhFilePath = moduPath <> ?fileExt
              doesFileExist edhFilePath >>= \case
                True ->
                  return $ Right (nomSpec, edhFilePath, edhFilePath)
                False -> do
                  let !edhIdxPath = moduPath </> ?frontFile
                  doesFileExist edhIdxPath >>= \case
                    True ->
                      return $ Right (nomSpec, moduPath, edhIdxPath)
                    False -> tryParentDir
      where
        tryParentDir =
          let !parentPkgPath = takeDirectory absPkgPath
           in if equalFilePath parentPkgPath absPkgPath
                then return $ Left $ "no such module: " <> T.pack (show nomSpec)
                else go parentPkgPath

locateEdhMainModule :: FilePath -> IO (Either Text (Text, FilePath, FilePath))
locateEdhMainModule !importPath = canonicalizePath "." >>= resolveMainImport
  where
    resolveMainImport :: FilePath -> IO (Either Text (Text, FilePath, FilePath))
    resolveMainImport !absPkgPath = do
      let !nomPath = absPkgPath </> "edh_modules" </> importPath
          !edhFilePath = nomPath </> "__main__.edh"
      doesFileExist edhFilePath >>= \case
        True -> return $ Right (T.pack importPath, nomPath, edhFilePath)
        False -> do
          let !parentPkgPath = takeDirectory absPkgPath
          if equalFilePath parentPkgPath absPkgPath
            then return $ Left $ "no such main module: " <> T.pack importPath
            else resolveMainImport parentPkgPath
