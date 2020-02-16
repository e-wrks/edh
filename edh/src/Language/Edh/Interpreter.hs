
module Language.Edh.Interpreter where


import           Prelude
-- import           Debug.Trace

import           Control.Exception
import           Control.Monad.IO.Class
import           Control.Monad.State.Strict
import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.Map.Strict               as Map

import           Text.Megaparsec

import           Language.Edh.Control
import           Language.Edh.Parser
import           Language.Edh.Runtime


createEdhModule :: MonadIO m => EdhWorld -> ModuleId -> m Object
createEdhModule world moduId = liftIO $ do
            -- prepare the module meta data
  !moduEntity <- newTVarIO $ Map.fromList
    [ (AttrByName "__name__", EdhString moduId)
    , (AttrByName "__file__", EdhString "<adhoc>")
    ]
  !moduSupers <- newTVarIO []
  return Object { objEntity = moduEntity
                , objClass  = moduleClass world
                , objSupers = moduSupers
                }


evalEdhSource
  :: MonadIO m
  => EdhWorld
  -> Object
  -> Text
  -> m (Either InterpretError EdhValue)
evalEdhSource world modu code = liftIO $ do
  mem <- readTVarIO (objEntity modu)
  let moduName = T.unpack $ case Map.lookup (AttrByName "__name__") mem of
        Just (EdhString name) -> name
        _                     -> "<adhoc>"
  -- serialize parsing against 'worldOperators'
  bracket (atomically $ takeTMVar wops) (atomically . tryPutTMVar wops)
    $ \opPD ->
        let (pr, opPD') = runState (runParserT parseProgram moduName code) opPD
        in  case pr of
              Left  !err   -> return $ Left $ EdhParseError err
              Right !stmts -> do

                -- trace
                --     ( (" ** parsed: \n" ++)
                --     $ unlines
                --     $ (<$> stmts) \(StmtSrc (sp, stmt)) ->
                --         sourcePosPretty sp ++ "\n  " ++ show stmt
                --     )
                --   $ return ()

                -- release world lock as soon as parsing done successfuly
                atomically $ putTMVar wops opPD'

                moduCtx <- atomically $ moduleContext world modu
                tryJust edhKnownError $ do
                  !final <- newEmptyTMVarIO
                  runEdhProgram' moduCtx
                    $ evalBlock stmts
                    $ \(OriginalValue !val _ _) ->
                        contEdhSTM $ putTMVar final val
                  atomically $ readTMVar final
  where !wops = worldOperators world
