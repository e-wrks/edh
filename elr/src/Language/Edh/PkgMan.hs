-- | Edh package management functionalities
module Language.Edh.PkgMan where

-- import           Debug.Trace

import Control.Exception (throwIO)
import Data.Dynamic (toDyn)
import Data.List (isPrefixOf, stripPrefix)
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

edhPkgPathFrom :: FilePath -> FilePath
edhPkgPathFrom !fromPath =
  if "<" `isPrefixOf` fromPath
    then "." -- intrinsic module path
    else case splitExtension fromPath of
      (filePath, ".edh") -> takeDirectory filePath
      _ -> fromPath

-- | returns import name, nominal path and actual file path, the last two will
-- be different e.g. in case an `__init__.edh` for a package, where nominal
-- path will  point to the root directory
locateEdhModule :: FilePath -> FilePath -> IO (ImportName, FilePath, FilePath)
locateEdhModule !pkgPath !nomSpec = case splitExtension nomSpec of
  (_, ".edh") ->
    throwPkgError
      "you don't include the `.edh` file extension in the import"
      [(AttrByName "spec", EdhString $ T.pack nomSpec)]
  _ ->
    doesPathExist pkgPath >>= \case
      False ->
        throwPkgError
          ("path does not exist: " <> T.pack pkgPath)
          [(AttrByName "path", EdhString $ T.pack pkgPath)]
      True -> case stripPrefix "./" nomSpec of
        Just !relImp -> resolveRelImport relImp
        Nothing -> canonicalizePath "." >>= resolveAbsImport
  where
    resolveRelImport :: FilePath -> IO (ImportName, FilePath, FilePath)
    resolveRelImport !relImp = do
      let !nomPath = (if null pkgPath then "." else pkgPath) </> relImp
          !edhFilePath = nomPath ++ ".edh"
      doesFileExist edhFilePath >>= \case
        True -> return (RelativeName (T.pack relImp), nomPath, edhFilePath)
        False -> do
          -- trace (" ** no hit: " <> edhFilePath <> " ** " <> nomPath) $ return ()
          let !edhIdxPath = nomPath </> "__init__.edh"
          doesFileExist edhIdxPath >>= \case
            True -> return (RelativeName (T.pack relImp), nomPath, edhIdxPath)
            False ->
              -- do
              --   trace (" ** no hit: " <> edhIdxPath <> " ** " <> nomPath) $  return ()
              throwPkgError
                ("no such module: " <> T.pack nomSpec)
                [(AttrByName "moduSpec", EdhString $ T.pack nomSpec)]

    resolveAbsImport :: FilePath -> IO (ImportName, FilePath, FilePath)
    resolveAbsImport !caniPkgPath = do
      let !nomPath = caniPkgPath </> "edh_modules" </> nomSpec
          !edhFilePath = nomPath ++ ".edh"
      -- trace (" ** no hit: " <> edhFilePath <> " ** " <> nomPath) $ return ()
      doesFileExist edhFilePath >>= \case
        True -> return (AbsoluteName (T.pack nomSpec), nomPath, edhFilePath)
        False -> do
          -- trace (" ** no hit: " <> edhFilePath <> " ** " <> nomPath) $ return ()
          let !edhIdxPath = nomPath </> "__init__.edh"
          doesFileExist edhIdxPath >>= \case
            True -> return (AbsoluteName (T.pack nomSpec), nomPath, edhIdxPath)
            False -> do
              -- trace (" ** no hit: " <> edhIdxPath <> " ** " <> nomPath) $ return ()
              let !parentPkgPath = takeDirectory caniPkgPath
              if equalFilePath parentPkgPath caniPkgPath
                then
                  throwPkgError
                    ("no such module: " <> T.pack nomSpec)
                    [(AttrByName "moduSpec", EdhString $ T.pack nomSpec)]
                else resolveAbsImport parentPkgPath

locateEdhMainModule :: FilePath -> IO (Text, FilePath, FilePath)
locateEdhMainModule !importPath = canonicalizePath "." >>= resolveMainImport
  where
    resolveMainImport :: FilePath -> IO (Text, FilePath, FilePath)
    resolveMainImport !caniPkgPath = do
      let !nomPath = caniPkgPath </> "edh_modules" </> importPath
          !edhFilePath = nomPath </> "__main__.edh"
      doesFileExist edhFilePath >>= \case
        True -> return (T.pack importPath, nomPath, edhFilePath)
        False -> do
          let !parentPkgPath = takeDirectory caniPkgPath
          if equalFilePath parentPkgPath caniPkgPath
            then
              throwPkgError
                ("no such main module: " <> T.pack importPath)
                [(AttrByName "importPath", EdhString $ T.pack importPath)]
            else resolveMainImport parentPkgPath
