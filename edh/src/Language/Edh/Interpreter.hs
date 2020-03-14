
module Language.Edh.Interpreter where


import           Prelude
-- import           Debug.Trace

import           Control.Exception
import           Control.Monad.IO.Class
import           Control.Monad.State.Strict
import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T

import           Text.Megaparsec

import           Language.Edh.Control
import           Language.Edh.Parser
import           Language.Edh.Runtime


parseEdhSource
  :: MonadIO m => EdhWorld -> Text -> Text -> m (Either EdhError [StmtSrc])
parseEdhSource !world !moduFileName !edhSource =
  liftIO -- serialize parsing against 'worldOperators'
    $ bracket (atomically $ takeTMVar wops) (atomically . tryPutTMVar wops)
    $ \opPD ->
        let (pr, opPD') = runState
              (runParserT parseProgram (T.unpack moduFileName) edhSource)
              opPD
        in  case pr of
              Left  !err   -> return $ Left $ EdhParseError err
              Right !stmts -> do
                -- release world lock as soon as parsing done successfuly
                atomically $ putTMVar wops opPD'
                return $ Right stmts
  where !wops = worldOperators world


evalEdhSource
  :: MonadIO m => EdhWorld -> Object -> Text -> m (Either EdhError EdhValue)
evalEdhSource !world !modu !edhSource = liftIO $ do
  let ent = objEntity modu
  moduFile <- liftIO $ atomically $ lookupEntityAttr ent (AttrByName "__file__")
  let moduFileName = case moduFile of
        EdhString !name -> name
        _               -> "<adhoc>"
  parseEdhSource world moduFileName edhSource >>= \case
    Left  !err   -> return $ Left err
    Right !stmts -> do
      let !moduCtx = moduleContext world modu
      tryJust edhKnownError $ do
        !final <- newEmptyTMVarIO
        runEdhProgram' moduCtx $ evalBlock stmts $ \(OriginalValue !val _ _) ->
          contEdhSTM $ putTMVar final val
        atomically $ readTMVar final

