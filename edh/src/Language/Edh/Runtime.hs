
module Language.Edh.Runtime where

import           Prelude
-- import           Debug.Trace

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Unique
import qualified Data.ByteString               as B
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Text.Encoding
import           Data.Text.Encoding.Error
import qualified Data.HashMap.Strict           as Map
import           Data.Dynamic

import           Text.Megaparsec

import           Data.Lossless.Decimal          ( decimalToInteger )

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Tx
import           Language.Edh.Details.PkgMan
import           Language.Edh.Details.Evaluate


createEdhWorld :: MonadIO m => EdhConsole -> m EdhWorld
createEdhWorld !console = liftIO $ do

  -- ultimate global artifacts go into this
  rootEntity <- atomically $ createHashEntity $ Map.fromList
    [ (AttrByName "__name__", EdhString "<root>")
    , (AttrByName "__file__", EdhString "<genesis>")
    , (AttrByName "__repr__", EdhString "<world>")
    , (AttrByName "None"    , edhNone)
    , (AttrByName "Nothing" , edhNothing)
    ]

  -- methods supporting reflected scope manipulation go into this
  scopeManiMethods <- atomically $ createHashEntity Map.empty

  -- prepare various pieces of the world
  rootSupers       <- newTVarIO []
  rootClassUniq    <- newUnique
  scopeClassUniq   <- newUnique
  let !rootClass = ProcDefi
        { procedure'uniq = rootClassUniq
        , procedure'lexi = Nothing
        , procedure'decl = ProcDecl { procedure'name = "<root>"
                                    , procedure'args = PackReceiver []
                                    , procedure'body = Right edhNop
                                    }
        }
      !root = Object { objEntity = rootEntity
                     , objClass  = rootClass
                     , objSupers = rootSupers
                     }
      !rootScope =
        Scope rootEntity root root defaultEdhExcptHndlr rootClass $ StmtSrc
          ( SourcePos { sourceName   = "<world-root>"
                      , sourceLine   = mkPos 1
                      , sourceColumn = mkPos 1
                      }
          , VoidStmt
          )
      !scopeClass = ProcDefi
        { procedure'uniq = scopeClassUniq
        , procedure'lexi = Just rootScope
        , procedure'decl = ProcDecl { procedure'name = "<scope>"
                                    , procedure'args = PackReceiver []
                                    , procedure'body = Right edhNop
                                    }
        }
  -- operator precedence dict
  opPD <- newTMVarIO $ Map.fromList
    [ ( "$" -- dereferencing attribute addressor
      , (10, "<Intrinsic>")
      )
    ]
  -- the container of loaded modules
  modus <- newTMVarIO Map.empty

  -- assembly the world with pieces prepared above
  let world = EdhWorld
        { worldScope     = rootScope
        , scopeSuper     = Object { objEntity = scopeManiMethods
                                  , objClass  = scopeClass
                                  , objSupers = rootSupers
                                  }
        , worldOperators = opPD
        , worldModules   = modus
        , worldConsole   = console
        }

  -- install host error classes, among which is "Exception" for Edh
  -- exception root class
  void $ runEdhProgram' (worldContext world) $ do
    pgs <- ask
    contEdhSTM $ do
      errClasses <- sequence
        -- leave the out-of-band entity store open so Edh code can
        -- assign arbitrary attrs to exceptions for informative
        [ (AttrByName nm, ) <$> mkHostClass rootScope nm False hc
        | (nm, hc) <- -- cross check with 'throwEdhSTM' for type safety
          [ ("ProgramHalt" , errCtor edhProgramHalt)
          , ("IOError"     , notFromEdhCtor)
          , ("Exception"   , errCtor $ edhSomeErr EdhException)
          , ("PackageError", errCtor $ edhSomeErr PackageError)
          , ("ParseError"  , errCtor $ edhSomeErr ParseError)
          , ("EvalError"   , errCtor $ edhSomeErr EvalError)
          , ("UsageError"  , errCtor $ edhSomeErr UsageError)
          ]
        ]
      updateEntityAttrs pgs rootEntity errClasses

  return world
 where
  edhProgramHalt :: ArgsPack -> EdhCallContext -> EdhError
  edhProgramHalt (ArgsPack [v] !kwargs) _ | Map.null kwargs =
    ProgramHalt $ toDyn v
  edhProgramHalt (ArgsPack [] !kwargs) _ | Map.null kwargs =
    ProgramHalt $ toDyn nil
  edhProgramHalt !apk _ = ProgramHalt $ toDyn $ EdhArgsPack apk
  edhSomeErr :: EdhErrorTag -> ArgsPack -> EdhCallContext -> EdhError
  edhSomeErr !et (ArgsPack [] _) !cc = EdhError et "❌" cc
  edhSomeErr !et (ArgsPack (EdhString msg : _) _) !cc = EdhError et msg cc
  edhSomeErr !et (ArgsPack (v : _) _) !cc = EdhError et (T.pack $ show v) cc
  notFromEdhCtor :: EdhHostCtor
  notFromEdhCtor _ _ _ !exit = exit $ toDyn nil
  -- wrap a Haskell error data constructor as a host error object contstructor,
  -- used to define an error class in Edh
  errCtor :: (ArgsPack -> EdhCallContext -> EdhError) -> EdhHostCtor
  errCtor !hec !pgs apk@(ArgsPack _ !kwargs) !obs !ctorExit = do
    let !unwind = case Map.lookup "unwind" kwargs of
          Just (EdhDecimal d) -> case decimalToInteger d of
            Just n -> fromIntegral n
            _      -> 1
          _ -> 1
        !cc = getEdhCallContext unwind pgs
        !he = hec apk cc
    edhErrorCtor (toException he) pgs apk obs ctorExit


declareEdhOperators :: EdhWorld -> Text -> [(OpSymbol, Precedence)] -> STM ()
declareEdhOperators world declLoc opps = do
  opPD  <- takeTMVar wops
  opPD' <-
    sequence
    $ Map.unionWithKey chkCompatible (return <$> opPD)
    $ Map.fromList
    $ (<$> opps)
    $ \(op, p) -> (op, return (p, declLoc))
  putTMVar wops opPD'
 where
  !wops = worldOperators world
  chkCompatible
    :: OpSymbol
    -> STM (Precedence, Text)
    -> STM (Precedence, Text)
    -> STM (Precedence, Text)
  chkCompatible op prev newly = do
    (prevPrec, prevDeclLoc) <- prev
    (newPrec , newDeclLoc ) <- newly
    if prevPrec /= newPrec
      then
        throwSTM
        $ EdhError
            UsageError
            (  "precedence change from "
            <> T.pack (show prevPrec)
            <> " (declared "
            <> prevDeclLoc
            <> ") to "
            <> T.pack (show newPrec)
            <> " (declared "
            <> T.pack (show newDeclLoc)
            <> ") for operator: "
            <> op
            )
        $ EdhCallContext "<edh>" []
      else return (prevPrec, prevDeclLoc)


createEdhModule :: MonadIO m => EdhWorld -> ModuleId -> String -> m Object
createEdhModule !world !moduId !srcName =
  liftIO $ atomically $ createEdhModule' world moduId srcName


installEdhModule
  :: MonadIO m
  => EdhWorld
  -> ModuleId
  -> (EdhProgState -> Object -> STM ())
  -> m Object
installEdhModule !world !moduId !preInstall = liftIO $ do
  modu <- createEdhModule world moduId "<host-code>"
  void $ runEdhProgram' (worldContext world) $ do
    pgs <- ask
    contEdhSTM $ do
      preInstall pgs modu
      moduSlot <- newTMVar $ EdhObject modu
      moduMap  <- takeTMVar (worldModules world)
      putTMVar (worldModules world) $ Map.insert moduId moduSlot moduMap
  return modu


haltEdhProgram :: EdhProgState -> EdhValue -> STM ()
haltEdhProgram !pgs !hv =
  edhErrorFrom pgs (toException $ ProgramHalt $ toDyn hv)
    $ \exv -> edhThrowSTM pgs exv


runEdhProgram :: MonadIO m => Context -> EdhProc -> m (Either EdhError EdhValue)
runEdhProgram !ctx !prog =
  liftIO $ tryJust edhKnownError $ runEdhProgram' ctx prog

runEdhProgram' :: MonadIO m => Context -> EdhProc -> m EdhValue
runEdhProgram' !ctx !prog = liftIO $ do
  haltResult <- atomically newEmptyTMVar
  driveEdhProgram haltResult ctx prog
  liftIO (atomically $ tryReadTMVar haltResult) >>= \case
    Nothing        -> return nil
    Just (Right v) -> return v
    Just (Left  e) -> throwIO e


runEdhModule
  :: MonadIO m => EdhWorld -> FilePath -> m (Either EdhError EdhValue)
runEdhModule !world !impPath =
  liftIO $ tryJust edhKnownError $ runEdhModule' world impPath

runEdhModule' :: MonadIO m => EdhWorld -> FilePath -> m EdhValue
runEdhModule' !world !impPath = liftIO $ do
  (nomPath, moduFile) <- locateEdhMainModule impPath
  fileContent <- streamDecodeUtf8With lenientDecode <$> B.readFile moduFile
  case fileContent of
    Some !moduSource _ _ -> runEdhProgram' (worldContext world) $ do
      pgs <- ask
      contEdhSTM $ do
        let !moduId = T.pack nomPath
        modu <- createEdhModule' world moduId moduFile
        runEdhProc pgs { edh'context = moduleContext world modu }
          $ evalEdh moduFile moduSource edhEndOfProc

