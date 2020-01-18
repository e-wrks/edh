
-- | Edh package management functionalities
module Language.Edh.Details.PkgMan where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           System.FilePath
import           System.Directory

import           Control.Concurrent.STM

import qualified Data.Text                     as T
import           Data.List

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes


edhPkgPathFrom :: FilePath -> FilePath
edhPkgPathFrom !fromPath = if "<" `isPrefixOf` fromPath
  then "" -- intrinsic module path
  else case splitExtension fromPath of
    (filePath, ".edh") -> takeDirectory filePath
    _                  -> fromPath


-- | returns nominal path and actual file path, the two will be different
-- e.g. in case an `__init__.edh` for a package, where nominal path will 
-- point to the root directory
locateEdhModule
  :: EdhProgState -> FilePath -> FilePath -> STM (FilePath, FilePath)
locateEdhModule !pgs !pkgPath !importPath = case splitExtension importPath of
  (_, ".edh") ->
    throwEdhSTM pgs EvalError
      $  "You don't include the `.edh` file extension in the import: "
      <> T.pack importPath
  _ -> unsafeIOToSTM (doesPathExist pkgPath) >>= \case
    False ->
      throwEdhSTM pgs EvalError $ "Path does not exist: " <> T.pack pkgPath
    True -> case stripPrefix "./" importPath of
      Just !relImp -> resolveRelImport relImp
      Nothing -> unsafeIOToSTM (canonicalizePath pkgPath) >>= resolveAbsImport
 where

  resolveRelImport :: FilePath -> STM (FilePath, FilePath)
  resolveRelImport !relImp = do
    let !nomPath     = (if null pkgPath then "." else pkgPath) </> relImp
        !edhFilePath = nomPath ++ ".edh"
    unsafeIOToSTM (doesFileExist edhFilePath) >>= \case
      True  -> return (nomPath, edhFilePath)
      False -> do
        -- trace (" ** no hit: " <> edhFilePath <> " ** " <> nomPath) $ return ()
        let !edhIdxPath = nomPath </> "__init__.edh"
        unsafeIOToSTM (doesFileExist edhIdxPath) >>= \case
          True -> return (nomPath, edhIdxPath)
          False ->
            -- do
            --   trace (" ** no hit: " <> edhIdxPath <> " ** " <> nomPath) $  return ()
            throwEdhSTM pgs EvalError
              $  "No such module: "
              <> T.pack importPath

  resolveAbsImport :: FilePath -> STM (FilePath, FilePath)
  resolveAbsImport caniPkgPath = do
    let !nomPath     = caniPkgPath </> "edh_modules" </> importPath
        !edhFilePath = nomPath ++ ".edh"
    -- trace (" ** no hit: " <> edhFilePath <> " ** " <> nomPath) $ return ()
    unsafeIOToSTM (doesFileExist edhFilePath) >>= \case
      True  -> return (nomPath, edhFilePath)
      False -> do
        -- trace (" ** no hit: " <> edhFilePath <> " ** " <> nomPath) $ return ()
        let !edhIdxPath = nomPath </> "__init__.edh"
        unsafeIOToSTM (doesFileExist edhIdxPath) >>= \case
          True  -> return (nomPath, edhIdxPath)
          False -> do
            -- trace (" ** no hit: " <> edhIdxPath <> " ** " <> nomPath) $ return ()
            let !parentPkgPath = takeDirectory caniPkgPath
            if equalFilePath parentPkgPath caniPkgPath
              then
                throwEdhSTM pgs EvalError
                $  "No such module: "
                <> T.pack importPath
              else resolveAbsImport parentPkgPath

