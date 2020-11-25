-- | Edh package management functionalities
module Language.Edh.PkgMan where

-- import Debug.Trace

import Control.Exception (throwIO)
import Data.Dynamic (toDyn)
import Data.List (isPrefixOf)
import Data.Text (Text)
import qualified Data.Text as T
import Language.Edh.Control
  ( EdhError (EdhError),
    EdhErrorTag (PackageError),
  )
import Language.Edh.IOPD (odFromList)
import Language.Edh.RtTypes
  ( ArgsPack (ArgsPack),
    AttrKey (AttrByName),
    EdhValue (EdhArgsPack, EdhString),
  )
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

-- package loading mechanism is kept as simple as possible by far, not Edh
-- program context trips into it, the `PackageError` thrown may be augmented
-- later when appropriate.
throwPkgError :: Text -> [(AttrKey, EdhValue)] -> IO a
throwPkgError !msg !details =
  throwIO $
    EdhError
      PackageError
      msg
      (toDyn $ EdhArgsPack $ ArgsPack [] $ odFromList details)
      "<os>"

edhRelPathFrom :: FilePath -> FilePath
edhRelPathFrom !fromPath =
  if "<" `isPrefixOf` fromPath
    then "." -- intrinsic module path
    else case splitExtension fromPath of
      (filePath, ".edh") -> takeDirectory filePath
      _ -> fromPath

-- | returns import name, nominal path and actual file path
--
-- there is a special case of `__init__.edh` for a dir module, where nominal
-- path will point to the directory, otherwise nominal path will be actual file
-- path without `.edh` extension
locateEdhModule :: FilePath -> FilePath -> IO (ImportName, FilePath, FilePath)
locateEdhModule !relPath !nomSpec = case splitExtension nomSpec of
  (_, ".edh") ->
    throwPkgError
      "you don't include the `.edh` file extension in the import"
      [(AttrByName "spec", EdhString $ T.pack nomSpec)]
  _ ->
    doesPathExist relPath >>= \case
      False ->
        throwPkgError
          ("path does not exist: " <> T.pack relPath)
          [(AttrByName "path", EdhString $ T.pack relPath)]
      True ->
        if "." `isPrefixOf` nomSpec
          then resolveRelImport nomSpec
          else canonicalizePath "." >>= resolveAbsImport
  where
    resolveRelImport :: FilePath -> IO (ImportName, FilePath, FilePath)
    resolveRelImport !relImp = do
      !nomPath <- canonicalizePath $ relPath </> relImp
      let !edhFilePath = nomPath <> ".edh"
      doesFileExist edhFilePath >>= \case
        True -> return (RelativeName (T.pack relImp), nomPath, edhFilePath)
        False -> do
          let !edhIdxPath = nomPath </> "__init__.edh"
          doesFileExist edhIdxPath >>= \case
            True -> return (RelativeName (T.pack relImp), nomPath, edhIdxPath)
            False ->
              throwPkgError
                ( "no such module: " <> T.pack (show nomSpec)
                    <> " relative to: "
                    <> T.pack relPath
                )
                [ (AttrByName "moduSpec", EdhString $ T.pack nomSpec),
                  (AttrByName "relPath", EdhString $ T.pack relPath)
                ]

    resolveAbsImport :: FilePath -> IO (ImportName, FilePath, FilePath)
    resolveAbsImport !absPkgPath =
      let !emsDir = absPkgPath </> "edh_modules"
       in doesDirectoryExist emsDir >>= \case
            False -> tryParentDir
            True -> do
              let !nomPath = emsDir </> nomSpec
                  !edhFilePath = nomPath <> ".edh"
              doesFileExist edhFilePath >>= \case
                True ->
                  return
                    ( AbsoluteName (T.pack nomSpec),
                      nomPath,
                      edhFilePath
                    )
                False -> do
                  let !edhIdxPath = nomPath </> "__init__.edh"
                  doesFileExist edhIdxPath >>= \case
                    True ->
                      return
                        ( AbsoluteName (T.pack nomSpec),
                          nomPath,
                          edhIdxPath
                        )
                    False -> tryParentDir
      where
        tryParentDir =
          let !parentPkgPath = takeDirectory absPkgPath
           in if equalFilePath parentPkgPath absPkgPath
                then
                  throwPkgError
                    ("no such module: " <> T.pack (show nomSpec))
                    [(AttrByName "moduSpec", EdhString $ T.pack nomSpec)]
                else resolveAbsImport parentPkgPath

locateEdhMainModule :: FilePath -> IO (Text, FilePath, FilePath)
locateEdhMainModule !importPath = canonicalizePath "." >>= resolveMainImport
  where
    resolveMainImport :: FilePath -> IO (Text, FilePath, FilePath)
    resolveMainImport !absPkgPath = do
      let !nomPath = absPkgPath </> "edh_modules" </> importPath
          !edhFilePath = nomPath </> "__main__.edh"
      doesFileExist edhFilePath >>= \case
        True -> return (T.pack importPath, nomPath, edhFilePath)
        False -> do
          let !parentPkgPath = takeDirectory absPkgPath
          if equalFilePath parentPkgPath absPkgPath
            then
              throwPkgError
                ("no such main module: " <> T.pack importPath)
                [(AttrByName "importPath", EdhString $ T.pack importPath)]
            else resolveMainImport parentPkgPath
