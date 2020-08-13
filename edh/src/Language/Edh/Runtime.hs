
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
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Tx
import           Language.Edh.Details.PkgMan
import           Language.Edh.Details.Evaluate


createEdhWorld :: MonadIO m => EdhConsole -> m EdhWorld
createEdhWorld !console = liftIO $ do

  -- ultimate global artifacts go into this
  rootEntity <- atomically $ createHashEntity =<< iopdFromList
    [ (AttrByName "__name__", EdhString "<root>")
    , (AttrByName "__file__", EdhString "<genesis>")
    , (AttrByName "__repr__", EdhString "<world>")
    , (AttrByName "None"    , edhNone)
    , (AttrByName "Nothing" , edhNothing)
    ]

  -- methods supporting reflected scope manipulation go into this
  scopeManiMethods <- atomically $ createHashEntity =<< iopdEmpty

  -- prepare various pieces of the world
  rootSupers       <- newTVarIO []
  rootClassUniq    <- newUnique
  scopeClassUniq   <- newUnique
  let !rootClass = ProcDefi
        { procedure'uniq = rootClassUniq
        , procedure'name = AttrByName "<root>"
        , procedure'lexi = Nothing
        , procedure'decl = ProcDecl { procedure'addr = NamedAttr "<root>"
                                    , procedure'args = PackReceiver []
                                    , procedure'body = Right edhNop
                                    }
        }
      !root = Object { objEntity = rootEntity
                     , objClass  = rootClass
                     , objSupers = rootSupers
                     }
      !rootScope = Scope
        { scopeEntity      = rootEntity
        , thisObject       = root
        , thatObject       = root
        , exceptionHandler = defaultEdhExcptHndlr
        , scopeProc        = rootClass
        , scopeCaller      = StmtSrc
                               ( SourcePos { sourceName   = "<world-root>"
                                           , sourceLine   = mkPos 1
                                           , sourceColumn = mkPos 1
                                           }
                               , VoidStmt
                               )
        , effectsStack     = []
        }
      !scopeClass = ProcDefi
        { procedure'uniq = scopeClassUniq
        , procedure'name = AttrByName "<scope>"
        , procedure'lexi = Just rootScope
        , procedure'decl = ProcDecl { procedure'addr = NamedAttr "<scope>"
                                    , procedure'args = PackReceiver []
                                    , procedure'body = Right edhNop
                                    }
        }
  -- operator precedence dict
  opPD  <- newTMVarIO $ Map.empty
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
        [ (AttrByName nm, )
            <$> (mkHostClass rootScope nm hc =<< createErrorObjSuper nm)
        | (nm, hc) <- -- cross check with 'throwEdhSTM' for type safety
          [ ("ProgramHalt" , errCtor edhProgramHalt)
          , ("IOError"     , fakableErr)
          , ("PeerError"   , fakableErr)
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
  edhProgramHalt (ArgsPack [v] !kwargs) _ | odNull kwargs =
    ProgramHalt $ toDyn v
  edhProgramHalt (ArgsPack [] !kwargs) _ | odNull kwargs =
    ProgramHalt $ toDyn nil
  edhProgramHalt !apk _ = ProgramHalt $ toDyn $ EdhArgsPack apk
  fakableErr :: EdhHostCtor
  fakableErr _ !apk !exit = exit $ toDyn apk
  edhSomeErr :: EdhErrorTag -> ArgsPack -> EdhCallContext -> EdhError
  edhSomeErr !et (ArgsPack [] _) !cc = EdhError et "❌" cc
  edhSomeErr !et (ArgsPack (EdhString msg : _) _) !cc = EdhError et msg cc
  edhSomeErr !et (ArgsPack (v : _) _) !cc = EdhError et (T.pack $ show v) cc
  -- wrap a Haskell error data constructor as a host error object contstructor,
  -- used to define an error class in Edh
  errCtor :: (ArgsPack -> EdhCallContext -> EdhError) -> EdhHostCtor
  errCtor !hec !pgs apk@(ArgsPack _ !kwargs) !ctorExit = do
    let !unwind = case odLookup (AttrByName "unwind") kwargs of
          Just (EdhDecimal d) -> case decimalToInteger d of
            Just n -> fromIntegral n
            _      -> 1
          _ -> 1
        !cc = getEdhCallContext unwind pgs
        !he = hec apk cc
    ctorExit $ toDyn (toException he, apk)


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


haltEdhProgram :: EdhProgState -> EdhValue -> STM ()
haltEdhProgram !pgs !hv = toEdhError pgs (toException $ ProgramHalt $ toDyn hv)
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


createEdhModule :: MonadIO m => EdhWorld -> ModuleId -> String -> m Object
createEdhModule !world !moduId !srcName =
  liftIO $ atomically $ createEdhModule' world moduId srcName


type EdhModulePreparation = EdhProgState -> STM () -> STM ()
edhModuleAsIs :: EdhModulePreparation
edhModuleAsIs _pgs !exit = exit


installEdhModule
  :: MonadIO m => EdhWorld -> ModuleId -> EdhModulePreparation -> m Object
installEdhModule !world !moduId !preInstall = liftIO $ do
  modu <- createEdhModule world moduId "<host-code>"
  void $ runEdhProgram' (worldContext world) $ do
    pgs <- ask
    let !moduCtx = moduleContext world modu
        !pgsModu = pgs { edh'context = moduCtx }
    contEdhSTM $ preInstall pgsModu $ do
      moduSlot <- newTMVar $ EdhObject modu
      moduMap  <- takeTMVar (worldModules world)
      putTMVar (worldModules world) $ Map.insert moduId moduSlot moduMap
  return modu

installedEdhModule :: MonadIO m => EdhWorld -> ModuleId -> m (Maybe Object)
installedEdhModule !world !moduId =
  liftIO $ atomically $ tryReadTMVar (worldModules world) >>= \case
    Nothing  -> return Nothing
    Just !mm -> case Map.lookup moduId mm of
      Nothing        -> return Nothing
      Just !moduSlot -> tryReadTMVar moduSlot >>= \case
        Just (EdhObject !modu) -> return $ Just modu
        _                      -> return Nothing


runEdhModule
  :: MonadIO m
  => EdhWorld
  -> FilePath
  -> EdhModulePreparation
  -> m (Either EdhError EdhValue)
runEdhModule !world !impPath !preRun =
  liftIO $ tryJust edhKnownError $ runEdhModule' world impPath preRun

runEdhModule'
  :: MonadIO m => EdhWorld -> FilePath -> EdhModulePreparation -> m EdhValue
runEdhModule' !world !impPath !preRun = liftIO $ do
  (nomPath, moduFile) <- locateEdhMainModule impPath
  fileContent <- streamDecodeUtf8With lenientDecode <$> B.readFile moduFile
  case fileContent of
    Some !moduSource _ _ -> runEdhProgram' (worldContext world) $ do
      pgs <- ask
      contEdhSTM $ do
        let !moduId = T.pack nomPath
        modu <- createEdhModule' world moduId moduFile
        let !moduCtx = moduleContext world modu
            !pgsModu = pgs { edh'context = moduCtx }
        preRun pgsModu $ runEdhProc pgsModu $ evalEdh moduFile
                                                      moduSource
                                                      endOfEdh


-- | perform an effectful call from current Edh context
--
-- if performing from an effectful procedure call, use the outer stack of
-- that call in effect resolution
--
-- otherwise this is the same as 'behaveEdhEffect'
performEdhEffect
  :: AttrKey
  -> [EdhValue]
  -> [(AttrName, EdhValue)]
  -> (EdhValue -> EdhProc)
  -> EdhProc
performEdhEffect !effKey !args !kwargs !exit = ask >>= \pgs ->
  contEdhSTM
    $ resolveEdhEffCallee pgs effKey edhTargetStackForPerform
    $ \(OriginalValue !effVal _ _, scopeMod) ->
        edhMakeCall'
            pgs
            effVal
            (thisObject $ contextScope $ edh'context pgs)
            ( ArgsPack args
            $ odFromList
            $ [ (AttrByName k, v) | (k, v) <- kwargs ]
            )
            scopeMod
          $ \mkCall ->
              runEdhProc pgs $ mkCall $ \(OriginalValue !rtnVal _ _) ->
                exit rtnVal

-- | obtain an effectful value from current Edh context
--
-- if performing from an effectful procedure call, use the outer stack of
-- that call in effect resolution
--
-- otherwise this is the same as 'behaveEdhEffect''
performEdhEffect' :: AttrKey -> (EdhValue -> EdhProc) -> EdhProc
performEdhEffect' !effKey !exit = ask >>= \ !pgs ->
  contEdhSTM $ resolveEdhPerform pgs effKey $ runEdhProc pgs . exit


-- | perform an effectful call from current Edh context
-- 
-- use full stack in effect resolution, may create infinite loops in effectful
-- procedure calls if one effectful procedure would make unconditional
-- recursive effectful call into itself, or there is some mutually recursive
-- pattern between multiple procedures
behaveEdhEffect
  :: AttrKey
  -> [EdhValue]
  -> [(AttrName, EdhValue)]
  -> (EdhValue -> EdhProc)
  -> EdhProc
behaveEdhEffect !effKey !args !kwargs !exit = ask >>= \pgs ->
  contEdhSTM
    $ resolveEdhEffCallee pgs effKey edhTargetStackForBehave
    $ \(OriginalValue !effVal _ _, scopeMod) ->
        edhMakeCall'
            pgs
            effVal
            (thisObject $ contextScope $ edh'context pgs)
            ( ArgsPack args
            $ odFromList
            $ [ (AttrByName k, v) | (k, v) <- kwargs ]
            )
            scopeMod
          $ \mkCall ->
              runEdhProc pgs $ mkCall $ \(OriginalValue !rtnVal _ _) ->
                exit rtnVal

-- | obtain an effectful value from current Edh context
--
-- use full stack in effect resolution
behaveEdhEffect' :: AttrKey -> (EdhValue -> EdhProc) -> EdhProc
behaveEdhEffect' !effKey !exit = ask >>= \ !pgs ->
  contEdhSTM $ resolveEdhBehave pgs effKey $ runEdhProc pgs . exit

