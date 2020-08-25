
-- | Edh package management functionalities
module Language.Edh.Details.PkgMan where

import           Prelude
-- import           Debug.Trace

import           System.FilePath
import           System.Directory

import           Control.Exception


import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.List
import           Data.Dynamic

import           Language.Edh.Control
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes


-- package loading mechanism is kept as simple as possible by far, not Edh
-- program context trips into it, the `PackageError` thrown may be augmented
-- later when appropriate.
throwPkgError :: Text -> [(AttrKey, EdhValue)] -> IO a
throwPkgError !msg !details =
  throwIO
    $ EdhError PackageError
               msg
               (toDyn $ EdhArgsPack $ ArgsPack [] $ odFromList details)
    $ EdhCallContext "<os>" []


edhPkgPathFrom :: FilePath -> FilePath
edhPkgPathFrom !fromPath = if "<" `isPrefixOf` fromPath
  then "." -- intrinsic module path
  else case splitExtension fromPath of
    (filePath, ".edh") -> takeDirectory filePath
    _                  -> fromPath


-- | returns nominal path and actual file path, the two will be different
-- e.g. in case an `__init__.edh` for a package, where nominal path will 
-- point to the root directory
locateEdhModule :: FilePath -> FilePath -> IO (FilePath, FilePath)
locateEdhModule !pkgPath !nomSpec = case splitExtension nomSpec of
  (_, ".edh") -> throwPkgError
    "you don't include the `.edh` file extension in the import"
    [(AttrByName "spec", EdhString $ T.pack nomSpec)]
  _ -> doesPathExist pkgPath >>= \case
    False -> throwPkgError "path does not exist"
                           [(AttrByName "path", EdhString $ T.pack pkgPath)]
    True -> case stripPrefix "./" nomSpec of
      Just !relImp -> resolveRelImport relImp
      Nothing      -> canonicalizePath "." >>= resolveAbsImport
 where

  resolveRelImport :: FilePath -> IO (FilePath, FilePath)
  resolveRelImport !relImp = do
    let !nomPath     = (if null pkgPath then "." else pkgPath) </> relImp
        !edhFilePath = nomPath ++ ".edh"
    doesFileExist edhFilePath >>= \case
      True  -> return (nomPath, edhFilePath)
      False -> do
        -- trace (" ** no hit: " <> edhFilePath <> " ** " <> nomPath) $ return ()
        let !edhIdxPath = nomPath </> "__init__.edh"
        doesFileExist edhIdxPath >>= \case
          True  -> return (nomPath, edhIdxPath)
          False ->
            -- do
            --   trace (" ** no hit: " <> edhIdxPath <> " ** " <> nomPath) $  return ()
                   throwPkgError
            "no such module"
            [(AttrByName "moduSpec", EdhString $ T.pack nomSpec)]

  resolveAbsImport :: FilePath -> IO (FilePath, FilePath)
  resolveAbsImport !caniPkgPath = do
    let !nomPath     = caniPkgPath </> "edh_modules" </> nomSpec
        !edhFilePath = nomPath ++ ".edh"
    -- trace (" ** no hit: " <> edhFilePath <> " ** " <> nomPath) $ return ()
    doesFileExist edhFilePath >>= \case
      True  -> return (nomPath, edhFilePath)
      False -> do
        -- trace (" ** no hit: " <> edhFilePath <> " ** " <> nomPath) $ return ()
        let !edhIdxPath = nomPath </> "__init__.edh"
        doesFileExist edhIdxPath >>= \case
          True  -> return (nomPath, edhIdxPath)
          False -> do
            -- trace (" ** no hit: " <> edhIdxPath <> " ** " <> nomPath) $ return ()
            let !parentPkgPath = takeDirectory caniPkgPath
            if equalFilePath parentPkgPath caniPkgPath
              then throwPkgError
                "no such module"
                [(AttrByName "moduSpec", EdhString $ T.pack nomSpec)]
              else resolveAbsImport parentPkgPath


locateEdhMainModule :: FilePath -> IO (FilePath, FilePath)
locateEdhMainModule !importPath = canonicalizePath "." >>= resolveMainImport
 where
  resolveMainImport :: FilePath -> IO (FilePath, FilePath)
  resolveMainImport !caniPkgPath = do
    let !nomPath     = caniPkgPath </> "edh_modules" </> importPath
        !edhFilePath = nomPath </> "__main__.edh"
    doesFileExist edhFilePath >>= \case
      True  -> return (nomPath, edhFilePath)
      False -> do
        let !parentPkgPath = takeDirectory caniPkgPath
        if equalFilePath parentPkgPath caniPkgPath
          then throwPkgError
            "no such main module"
            [(AttrByName "importPath", EdhString $ T.pack importPath)]
          else resolveMainImport parentPkgPath

