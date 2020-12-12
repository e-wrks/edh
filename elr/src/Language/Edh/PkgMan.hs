-- | Edh package management functionalities
module Language.Edh.PkgMan where

-- import Debug.Trace

import Data.List (isPrefixOf)
import Data.Text (Text)
import qualified Data.Text as T
import System.Directory
  ( canonicalizePath,
    doesDirectoryExist,
    doesFileExist,
    doesPathExist,
  )
import System.FilePath
  ( equalFilePath,
    splitExtension,
    takeDirectory,
    (</>),
  )
import Prelude

data ImportName = RelativeName !Text | AbsoluteName !Text

edhRelativePathFrom :: FilePath -> FilePath
edhRelativePathFrom !fromPath =
  if "<" `isPrefixOf` fromPath
    then "." -- intrinsic module path
    else case splitExtension fromPath of
      (filePath, ".edh") -> takeDirectory filePath
      _ -> fromPath

-- | returns import name, absolute module path and absolute file
--
-- there is a special case of `__init__.edh` for a dir module, where nominal
-- path will point to the directory, otherwise nominal path will be actual file
-- path without `.edh` extension
locateEdhModule ::
  Text ->
  FilePath ->
  IO (Either Text (ImportName, FilePath, FilePath))
locateEdhModule !nomSpec !relPath = case splitExtension (T.unpack nomSpec) of
  (_, ".edh") ->
    return $
      Left "you don't include the `.edh` file extension in the import"
  _ ->
    doesPathExist relPath >>= \case
      False ->
        return $
          Left $ "path does not exist: " <> T.pack relPath
      True ->
        if "." `T.isPrefixOf` nomSpec
          then
            fmap (\(!name, !path, !file) -> (RelativeName name, path, file))
              <$> resolveRelativeImport nomSpec relPath
          else
            fmap (\(!name, !path, !file) -> (AbsoluteName name, path, file))
              <$> resolveAbsoluteImport nomSpec "."

resolveRelativeImport ::
  Text ->
  FilePath ->
  IO (Either Text (Text, FilePath, FilePath))
resolveRelativeImport !nomSpec !relPath = do
  !nomPath <- canonicalizePath $ relPath </> relImp
  let !edhFilePath = nomPath <> ".edh"
  doesFileExist edhFilePath >>= \case
    True -> return $ Right (nomSpec, edhFilePath, edhFilePath)
    False ->
      let !edhIdxPath = nomPath </> "__init__.edh"
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
              let !edhFilePath = moduPath <> ".edh"
              doesFileExist edhFilePath >>= \case
                True ->
                  return $ Right (nomSpec, edhFilePath, edhFilePath)
                False -> do
                  let !edhIdxPath = moduPath </> "__init__.edh"
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
