module Language.Edh.RuntimeM where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import qualified Data.HashMap.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Language.Edh.Evaluate
import Language.Edh.Monad
import Language.Edh.RtTypes
import Language.Edh.Runtime
import Prelude

installEdhModuleM :: EdhWorld -> Text -> Edh () -> IO Object
installEdhModuleM !world !moduName !preInstall = do
  !modu <-
    createEdhModule world moduName $ T.unpack $ "<host:" <> moduName <> ">"
  void $
    runEdhProgram' world $ \ !ets ->
      moduleContext world modu >>= \ !moduCtx ->
        runEdh ets {edh'context = moduCtx} preInstall $ \_ _ets -> do
          !moduSlot <- newTVar $ ModuLoaded modu
          !moduMap <- takeTMVar (edh'world'modules world)
          putTMVar (edh'world'modules world) $
            Map.insert (HostModule moduName) moduSlot moduMap
  return modu
