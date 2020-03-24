
module Language.Edh.Runtime where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           System.IO                      ( stderr )
import           System.Environment
import           Text.Read

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader

import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Unique
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE
import qualified Data.ByteString               as B
import           Data.Text.IO
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Text.Encoding
import           Data.Text.Encoding.Error
import qualified Data.HashMap.Strict           as Map

import           Text.Megaparsec

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Tx
import           Language.Edh.Details.PkgMan
import           Language.Edh.Details.Evaluate


-- | This runtime serializes all log messages to 'stderr' through a 'TQueue',
-- this is crucial under heavy concurrency.
--
-- `ioChan` is used to facilitate command input/output via 'stdin'/'stdout',
-- an io loop run by main thread using a library like `haskeline` is assumed.
--
-- known issues:
--  *) can mess up with others writing to 'stderr'
--  *) if all others use 'trace' only, there're minimum messups but emojis 
--     seem to be break points
defaultEdhRuntime :: TQueue EdhConsoleIO -> IO EdhRuntime
defaultEdhRuntime !ioQ = do
  envLogLevel <- lookupEnv "EDH_LOG_LEVEL"
  logIdle     <- newEmptyTMVarIO
  logQueue    <- newTQueueIO
  let logLevel = case envLogLevel of
        Nothing      -> 20
        Just "DEBUG" -> 10
        Just "INFO"  -> 20
        Just "WARN"  -> 30
        Just "ERROR" -> 40
        Just "FATAL" -> 50
        Just ns      -> case readEither ns of
          Left  _           -> 0
          Right (ln :: Int) -> ln
      flushLogs :: IO ()
      flushLogs = atomically $ readTMVar logIdle
      logPrinter :: IO ()
      logPrinter = do
        lr <- atomically (tryReadTQueue logQueue) >>= \case
          Just !lr -> do
            void $ atomically $ tryTakeTMVar logIdle
            return lr
          Nothing -> do
            void $ atomically $ tryPutTMVar logIdle ()
            lr <- atomically $ readTQueue logQueue
            void $ atomically $ tryTakeTMVar logIdle
            return lr
        hPutStrLn stderr lr
        logPrinter
      logger :: EdhLogger
      logger !level !srcLoc !pkargs = do
        void $ tryTakeTMVar logIdle
        case pkargs of
          ArgsPack [!argVal] !kwargs | Map.null kwargs ->
            writeTQueue logQueue $! T.pack logPrefix <> logString argVal
          -- todo: format structured log record with log parser in mind
          _ -> writeTQueue logQueue $! T.pack $ logPrefix ++ show pkargs
       where
        logString :: EdhValue -> Text
        logString (EdhString s) = s
        logString v             = T.pack $ show v
        logPrefix :: String
        logPrefix =
          (case srcLoc of
              Nothing -> id
              Just sl -> (++ sl ++ "\n")
            )
            $ case level of
                _ | level >= 50 -> "🔥 "
                _ | level >= 40 -> "❗ "
                _ | level >= 30 -> "⚠️ "
                _ | level >= 20 -> "ℹ️ "
                _ | level >= 10 -> "🐞 "
                _               -> "😥 "
  void $ mask_ $ forkIOWithUnmask $ \unmask ->
    finally (unmask logPrinter) $ atomically $ tryPutTMVar logIdle ()
  return EdhRuntime { consoleIO        = ioQ
                    , runtimeLogLevel  = logLevel
                    , runtimeLogger    = logger
                    , flushRuntimeLogs = flushLogs
                    }


createEdhWorld :: MonadIO m => EdhRuntime -> m EdhWorld
createEdhWorld !runtime = liftIO $ do
  -- ultimate default methods/operators/values go into this
  rootEntity <- atomically $ createHashEntity $ Map.fromList
    [ (AttrByName "__name__", EdhString "<root>")
    , (AttrByName "__file__", EdhString "<genesis>")
    , (AttrByName "__repr__", EdhString "<world>")
    , (AttrByName "None"    , edhNone)
    , (AttrByName "Nothing" , edhNothing)
    ]
  -- methods supporting reflected scope manipulation go into this
  scopeManiMethods <- atomically $ createHashEntity Map.empty
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
      !rootScope = Scope rootEntity root root rootClass $ StmtSrc
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
  opPD <- newTMVarIO $ Map.fromList
    [ ( "$" -- dereferencing attribute addressor
      , (10, "<Intrinsic>")
      )
    ]
  modus <- newTMVarIO Map.empty
  return $ EdhWorld
    { worldScope     = rootScope
    , scopeSuper     = Object { objEntity = scopeManiMethods
                              , objClass  = scopeClass
                              , objSupers = rootSupers
                              }
    , worldOperators = opPD
    , worldModules   = modus
    , worldRuntime   = runtime
    }


declareEdhOperators :: EdhWorld -> Text -> [(OpSymbol, Precedence)] -> STM ()
declareEdhOperators world declLoc opps = do
  opPD <- takeTMVar wops
  catchSTM (declarePrecedence opPD)
    $ \(e :: SomeException) -> tryPutTMVar wops opPD >> throwSTM e
 where
  !wops = worldOperators world
  declarePrecedence :: OpPrecDict -> STM ()
  declarePrecedence opPD = do
    opPD' <-
      sequence
      $ Map.unionWithKey chkCompatible (return <$> opPD)
      $ Map.fromList
      $ (<$> opps)
      $ \(op, p) -> (op, return (p, declLoc))
    putTMVar wops opPD'
  chkCompatible
    :: OpSymbol
    -> STM (Precedence, Text)
    -> STM (Precedence, Text)
    -> STM (Precedence, Text)
  chkCompatible op prev newly = do
    (prevPrec, prevDeclLoc) <- prev
    (newPrec , newDeclLoc ) <- newly
    if newPrec < 0 || newPrec >= 10
      then
        throwSTM
        $ UsageError
            (  "Invalidate precedence "
            <> T.pack (show newPrec)
            <> " (declared "
            <> T.pack (show newDeclLoc)
            <> ") for operator: "
            <> op
            )
        $ EdhCallContext "<edh>" []
      else if prevPrec /= newPrec
        then
          throwSTM
          $ UsageError
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


mkIntrinsicOp :: EdhWorld -> OpSymbol -> EdhIntrinsicOp -> STM EdhValue
mkIntrinsicOp !world !opSym !iop = do
  u <- unsafeIOToSTM newUnique
  Map.lookup opSym <$> readTMVar (worldOperators world) >>= \case
    Nothing ->
      throwSTM
        $ UsageError
            ("No precedence declared in the world for operator: " <> opSym)
        $ EdhCallContext "<edh>" []
    Just (preced, _) -> return $ EdhIntrOp preced $ IntrinOpDefi u opSym iop

mkHostProc
  :: Scope
  -> (ProcDefi -> EdhValue)
  -> Text
  -> EdhProcedure
  -> ArgsReceiver
  -> STM EdhValue
mkHostProc !scope !vc !nm !p !args = do
  u <- unsafeIOToSTM newUnique
  return $ vc ProcDefi
    { procedure'uniq = u
    , procedure'lexi = Just scope
    , procedure'decl = ProcDecl { procedure'name = nm
                                , procedure'args = args
                                , procedure'body = Right p
                                }
    }

mkHostClass
  :: Scope -- ^ outer lexical scope
  -> Text  -- ^ class name
  -> Bool  -- ^ write protect the out-of-band attribute store
  -> (  EdhProgState
     -> ArgsPack
     -> TVar (Map.HashMap AttrKey EdhValue)  -- out-of-band attr store 
     -> STM ()
     )
  -> STM EdhValue
mkHostClass !scope !nm !writeProtected !hc = do
  classUniq <- unsafeIOToSTM newUnique
  let
    !cls = ProcDefi
      { procedure'uniq = classUniq
      , procedure'lexi = Just scope
      , procedure'decl = ProcDecl { procedure'name = nm
                                  , procedure'args = PackReceiver []
                                  , procedure'body = Right ctor
                                  }
      }
    ctor :: EdhProcedure
    ctor !apk !exit = do
      -- note: cross check logic here with `createEdhObject`
      pgs <- ask
      contEdhSTM $ do
        (ent, obs) <- createSideEntity writeProtected
        !newThis   <- viewAsEdhObject ent cls []
        let ctx       = edh'context pgs
            pgsCtor   = pgs { edh'context = ctorCtx }
            ctorCtx   = ctx { callStack = ctorScope :| NE.tail (callStack ctx) }
            ctorScope = Scope { scopeEntity = ent
                              , thisObject  = newThis
                              , thatObject  = newThis
                              , scopeProc   = cls
                              , scopeCaller = contextStmt ctx
                              }
        hc pgsCtor apk obs
        exitEdhSTM pgs exit $ EdhObject newThis
  return $ EdhClass cls


runEdhProgram
  :: MonadIO m => Context -> EdhProg (STM ()) -> m (Either EdhError EdhValue)
runEdhProgram !ctx !prog =
  liftIO $ tryJust edhKnownError $ runEdhProgram' ctx prog

runEdhProgram' :: MonadIO m => Context -> EdhProg (STM ()) -> m EdhValue
runEdhProgram' !ctx !prog = liftIO $ do
  haltResult <- atomically newEmptyTMVar
  driveEdhProgram haltResult ctx prog
  liftIO (atomically $ tryReadTMVar haltResult) >>= \case
    Nothing        -> return nil
    Just (Right v) -> return v
    Just (Left  e) -> throwIO e


runEdhModule :: MonadIO m => EdhWorld -> FilePath -> m (Either EdhError ())
runEdhModule !world !impPath =
  liftIO $ tryJust edhKnownError $ runEdhModule' world impPath

runEdhModule' :: MonadIO m => EdhWorld -> FilePath -> m ()
runEdhModule' !world !impPath = liftIO $ do
  (nomPath, moduFile) <- locateEdhMainModule impPath
  fileContent <- streamDecodeUtf8With lenientDecode <$> B.readFile moduFile
  case fileContent of
    Some !moduSource _ _ -> void $ runEdhProgram' (worldContext world) $ do
      pgs <- ask
      contEdhSTM $ do
        let !moduId = T.pack nomPath
        modu <- createEdhModule' world moduId moduFile
        runEdhProg pgs { edh'context = moduleContext world modu }
          $ evalEdh moduFile moduSource edhEndOfProc


bootEdhModule :: MonadIO m => EdhWorld -> Text -> m (Either EdhError Object)
bootEdhModule !world !impSpec = liftIO $ tryJust edhKnownError $ do
  !final <- newEmptyTMVarIO
  void
    $ runEdhProgram' (worldContext world)
    $ importEdhModule impSpec
    $ \(OriginalValue !val _ _) -> case val of
        EdhObject !modu -> contEdhSTM $ putTMVar final modu
        _               -> error "bug: importEdhModule returns non-object?"
  atomically (tryReadTMVar final) >>= \case
    Just modu -> return modu -- a bit more informative than stm deadlock
    Nothing ->
      throwIO $ UsageError "Module not loaded." $ EdhCallContext "<edh>" []

