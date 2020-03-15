
module Language.Edh.Runtime
  ( createEdhWorld
  , defaultEdhLogger
  , bootEdhModule
  , runEdhProgram
  , runEdhProgram'
  , createEdhModule
  , installEdhModule
  , declareEdhOperators
  , mkHostProc
  , mkHostClass
  , mkHostOper
  , module CL
  , module RT
  , module TX
  , module EV
  )
where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           System.IO                      ( stderr )

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader

import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Unique
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE
import           Data.Text.IO
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

import           Text.Megaparsec

import           Language.Edh.Control
import           Language.Edh.Details.CoreLang as CL
import           Language.Edh.Details.RtTypes  as RT
import           Language.Edh.Details.Tx       as TX
import           Language.Edh.Details.Evaluate as EV


bootEdhModule :: MonadIO m => EdhWorld -> Text -> m (Either EdhError Object)
bootEdhModule !world impSpec = liftIO $ tryJust edhKnownError $ do
  !final <- newEmptyTMVarIO
  runEdhProgram' (worldContext world)
    $ importEdhModule impSpec
    $ \(OriginalValue !val _ _) -> case val of
        EdhObject !modu -> contEdhSTM $ putTMVar final modu
        _               -> error "bug: importEdhModule returns non-object?"
  atomically $ readTMVar final


runEdhProgram
  :: MonadIO m => Context -> EdhProg (STM ()) -> m (Either EdhError ())
runEdhProgram !ctx !prog =
  liftIO $ tryJust edhKnownError $ runEdhProgram' ctx prog

runEdhProgram' :: MonadIO m => Context -> EdhProg (STM ()) -> m ()
runEdhProgram' !ctx !prog = liftIO $ do
  haltResult <- atomically newEmptyTMVar
  driveEdhProgram haltResult ctx prog


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
  rootEntity <- atomically $ createHashEntity $ Map.fromList
    [ (AttrByName "__name__", EdhString "<root>")
    , (AttrByName "__file__", EdhString "<genesis>")
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
      !rootScope  = Scope rootEntity root root rootClass
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
  modus   <- newTMVarIO Map.empty
  runtime <- newTMVarIO EdhRuntime { runtimeLogger   = logger
                                   , runtimeLogLevel = 20
                                   }
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


createEdhModule :: MonadIO m => EdhWorld -> ModuleId -> String -> m Object
createEdhModule !world !moduId !moduSrc = liftIO $ do
  -- prepare the module meta data
  !moduEntity <- atomically $ createHashEntity $ Map.fromList
    [ (AttrByName "__name__", EdhString moduId)
    , (AttrByName "__file__", EdhString $ T.pack moduSrc)
    ]
  !moduSupers    <- newTVarIO []
  !moduClassUniq <- newUnique
  return Object
    { objEntity = moduEntity
    , objClass  = ProcDefi
                    { procedure'uniq = moduClassUniq
                    , procedure'lexi = Just $ worldScope world
                    , procedure'decl = ProcDecl
                      { procedure'name = "module:" <> moduId
                      , procedure'args = PackReceiver []
                      , procedure'body = Left $ StmtSrc
                                           ( SourcePos { sourceName   = moduSrc
                                                       , sourceLine   = mkPos 1
                                                       , sourceColumn = mkPos 1
                                                       }
                                           , VoidStmt
                                           )
                      }
                    }
    , objSupers = moduSupers
    }

installEdhModule
  :: MonadIO m
  => EdhWorld
  -> ModuleId
  -> (EdhProgState -> Object -> STM ())
  -> m Object
installEdhModule !world !moduId !preInstall = liftIO $ do
  modu <- createEdhModule world moduId "<host-code>"
  runEdhProgram' (worldContext world) $ do
    pgs <- ask
    contEdhSTM $ do
      preInstall pgs modu
      moduSlot <- newTMVar $ EdhObject modu
      moduMap  <- takeTMVar (worldModules world)
      putTMVar (worldModules world) $ Map.insert moduId moduSlot moduMap
  return modu


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
     -> ArgsSender
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
    ctor !argsSndr !exit = do
      -- note: cross check logic here with `createEdhObject`
      pgs <- ask
      contEdhSTM $ do
        (ent, obs) <- createSideEntity writeProtected
        !newThis   <- viewAsEdhObject ent cls []
        let ctx       = edh'context pgs
            pgsCtor   = pgs { edh'context = ctorCtx }
            ctorCtx   = ctx { callStack = ctorScope :| NE.tail (callStack ctx) }
            ctorScope = (contextScope ctx) { scopeEntity = ent
                                           , thisObject  = newThis
                                           , thatObject  = newThis
                                           }
        hc pgsCtor argsSndr obs
        exitEdhSTM pgs exit $ EdhObject newThis
  return $ EdhClass cls

mkHostOper :: EdhWorld -> Scope -> OpSymbol -> EdhProcedure -> STM EdhValue
mkHostOper !world !scope !opSym !hp = do
  u <- unsafeIOToSTM newUnique
  Map.lookup opSym <$> readTMVar (worldOperators world) >>= \case
    Nothing ->
      throwSTM
        $  UsageError
        $  "No precedence declared in the world for operator: "
        <> opSym
    Just (prec, _) -> return $ EdhOperator
      prec
      Nothing
      ProcDefi
        { procedure'uniq = u
        , procedure'lexi = Just scope
        , procedure'decl = ProcDecl
          { procedure'name = opSym
          , procedure'args = PackReceiver
            [RecvArg "lhv" Nothing Nothing, RecvArg "rhv" Nothing Nothing]
          , procedure'body = Right hp
          }
        }

