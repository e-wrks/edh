
module Language.Edh.Runtime
  ( createEdhWorld
  , defaultEdhLogger
  , declareEdhOperators
  , installEdhAttrs
  , installEdhAttr
  , bootEdhModule
  , runEdhProgram
  , runEdhProgram'
  , mkHostProc
  , mkHostOper
  , module CL
  , module RT
  , module TX
  , module EV
  )
where

import           Prelude
-- import           Debug.Trace

import           System.IO                      ( stderr )
import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Exception
import           Control.Monad.Except

import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Unique
import           Data.Text.IO
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

import           Language.Edh.Control
import           Language.Edh.Details.CoreLang as CL
import           Language.Edh.Details.RtTypes  as RT
import           Language.Edh.Details.Tx       as TX
import           Language.Edh.Details.Evaluate as EV


bootEdhModule
  :: MonadIO m => EdhWorld -> Text -> m (Either InterpretError Object)
bootEdhModule !world impSpec = liftIO $ tryJust edhKnownError $ do
  !final <- newEmptyTMVarIO
  runEdhProgram' (worldContext world)
    $ importEdhModule (SingleReceiver (RecvRestPkArgs "_")) impSpec
    $ \(OriginalValue !val _ _) -> case val of
        EdhObject modu -> contEdhSTM $ putTMVar final modu
        _              -> error "bug: importEdhModule returns non-object?"
  atomically $ readTMVar final


runEdhProgram
  :: MonadIO m => Context -> EdhProg (STM ()) -> m (Either InterpretError ())
runEdhProgram !ctx !prog =
  liftIO $ tryJust edhKnownError $ runEdhProgram' ctx prog

runEdhProgram' :: MonadIO m => Context -> EdhProg (STM ()) -> m ()
runEdhProgram' !ctx !prog = liftIO $ driveEdhProgram ctx prog


-- | This logger serializes all log messages to 'stderr' through a 'TQueue',
-- this is crucial under heavy concurrency.
--
-- known issues:
--  *) can mess up with others writing to 'stderr'
--  *) if all others use 'trace' only, there're minimum messups but emojis 
--     seem to be break points
defaultEdhLogger :: IO EdhLogger
defaultEdhLogger = do
  logQueue <- newTQueueIO
  let logPrinter :: IO ()
      logPrinter = do
        msg <- atomically $ readTQueue logQueue
        hPutStrLn stderr msg
        logPrinter
      logger :: EdhLogger
      logger !level !srcLoc !pkargs = case pkargs of
        ArgsPack [!argVal] !kwargs | Map.null kwargs ->
          writeTQueue logQueue $! T.pack logPrefix <> edhValueStr argVal
        _ -> writeTQueue logQueue $! T.pack $ logPrefix ++ show pkargs
       where
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
  void $ forkIO logPrinter
  return logger


createEdhWorld :: MonadIO m => EdhLogger -> m EdhWorld
createEdhWorld !logger = liftIO $ do
  -- ultimate default methods/operators/values go into this
  rootEntity <- atomically $ createEntity $ Map.fromList
    [ (AttrByName "__name__", EdhString "<root>")
    , (AttrByName "__file__", EdhString "<Genesis>")
    ]
  -- methods supporting reflected scope manipulation go into this
  scopeManiMethods <- atomically $ createEntity Map.empty
  rootSupers       <- newTVarIO []
  rootClassUniq    <- newUnique
  moduClassUniq    <- newUnique
  scopeClassUniq   <- newUnique
  let !rootClass = ProcDefi
        { procedure'lexi = Nothing
        , procedure'decl = ProcDecl { procedure'uniq = rootClassUniq
                                    , procedure'name = "<genesis>"
                                    , procedure'args = WildReceiver
                                    , procedure'body = voidStatement
                                    }
        }
      !root = Object { objEntity = rootEntity
                     , objClass  = rootClass
                     , objSupers = rootSupers
                     }
      !rootScope = Scope rootEntity root root rootClass
      !moduClass = ProcDefi
        { procedure'lexi = Just rootScope
        , procedure'decl = ProcDecl { procedure'uniq = moduClassUniq
                                    , procedure'name = "<module>"
                                    , procedure'args = WildReceiver
                                    , procedure'body = voidStatement
                                    }
        }
      !scopeClass = ProcDefi
        { procedure'lexi = Just rootScope
        , procedure'decl = ProcDecl { procedure'uniq = scopeClassUniq
                                    , procedure'name = "<scope>"
                                    , procedure'args = WildReceiver
                                    , procedure'body = voidStatement
                                    }
        }
  opPD <- newTMVarIO $ Map.fromList
    [ ( "$" -- dereferencing attribute addressor
      , (10, "<Intrinsic>")
      )
    ]
  modus   <- newTMVarIO Map.empty
  runtime <- newTMVarIO EdhRuntime { runtimeLogger   = logger
                                   , runtimeLogLevel = 20
                                   }
  return $ EdhWorld
    { moduleClass    = moduClass
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
        $  UsageError
        $  "Invalidate precedence "
        <> T.pack (show newPrec)
        <> " (declared "
        <> T.pack (show newDeclLoc)
        <> ") for operator: "
        <> op
      else if prevPrec /= newPrec
        then throwSTM $ UsageError
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
        else return (prevPrec, prevDeclLoc)


mkHostProc
  :: (HostProcedure -> EdhValue) -> Text -> EdhProcedure -> STM EdhValue
mkHostProc !vc !n !p = do
  !u <- unsafeIOToSTM $ newUnique
  return $ vc $ HostProcedure { hostProc'uniq = u
                              , hostProc'name = n
                              , hostProc'proc = p
                              }

mkHostOper :: EdhWorld -> OpSymbol -> EdhProcedure -> STM EdhValue
mkHostOper world opSym proc =
  Map.lookup opSym <$> readTMVar (worldOperators world) >>= \case
    Nothing ->
      throwSTM
        $  UsageError
        $  "No precedence declared in the world for operator: "
        <> opSym
    Just (prec, _) -> do
      !u <- unsafeIOToSTM newUnique
      return $ EdhHostOper prec $ HostProcedure u opSym proc


installEdhAttrs :: Entity -> [(AttrKey, EdhValue)] -> STM ()
installEdhAttrs e as = modifyTVar' (entity'store e) $ \em -> Map.union ad em
  where ad = Map.fromList as

installEdhAttr :: Entity -> AttrKey -> EdhValue -> STM ()
installEdhAttr e k v = modifyTVar' (entity'store e) $ \em -> Map.insert k v em
