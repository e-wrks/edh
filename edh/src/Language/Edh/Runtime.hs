
module Language.Edh.Runtime where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Unique
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE
import qualified Data.ByteString               as B
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Text.Encoding
import           Data.Text.Encoding.Error
import qualified Data.HashMap.Strict           as Map
import           Data.Dynamic

import           Text.Megaparsec

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Tx
import           Language.Edh.Details.PkgMan
import           Language.Edh.Details.Evaluate


createEdhWorld :: MonadIO m => EdhRuntime -> m EdhWorld
createEdhWorld !runtime = liftIO $ do

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
      !rootScope = Scope rootEntity root root [] rootClass $ StmtSrc
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
        , worldRuntime   = runtime
        }

  -- install host error classes
  void $ runEdhProgram' (worldContext world) $ do
    pgs <- ask
    contEdhSTM $ do
      errClasses <- sequence
        [ (AttrByName nm, ) <$> mkHostClass rootScope nm False hc
        | (nm, hc) <-
          [ ("ProgramHalt" , edhErrorCtor edhProgramHaltCtor)
          , ("PackageError", edhErrorCtor $ edhCommonErrCtor PackageError)
          , ("ParseError"  , edhErrorCtor $ edhCommonErrCtor ParseError)
          , ("EvalError"   , edhErrorCtor $ edhCommonErrCtor EvalError)
          , ("UsageError"  , edhErrorCtor $ edhCommonErrCtor UsageError)
          ]
        ]
      updateEntityAttrs pgs rootEntity errClasses

  return world
 where
  edhProgramHaltCtor :: ArgsPack -> EdhCallContext -> EdhError
  edhProgramHaltCtor (ArgsPack [v] !kwargs) _ | Map.null kwargs =
    ProgramHalt $ toDyn v
  edhProgramHaltCtor !apk _ = ProgramHalt $ toDyn apk
  edhCommonErrCtor
    :: (Text -> EdhCallContext -> EdhError)
    -> ArgsPack
    -> EdhCallContext
    -> EdhError
  edhCommonErrCtor !ec (ArgsPack []      _) !cc = ec "" cc
  edhCommonErrCtor !ec (ArgsPack (v : _) _) !cc = ec (T.pack $ show v) cc
  -- wrap a Haskell error data constructor as a host error object contstructor,
  -- used to define an error class in Edh 
  edhErrorCtor :: (ArgsPack -> EdhCallContext -> EdhError) -> EdhHostCtor
  edhErrorCtor !hec !pgs !apk !obs = do
    let !scope = contextScope $ edh'context pgs
        !this  = thisObject scope
        !cc    = getEdhCallContext 1 pgs
        !he    = hec apk cc
        __init__ :: EdhProcedure
        __init__ _ !exit =
          ask -- need to do nothing but return `this`
            >>= exitEdhProc exit
            .   EdhObject
            .   thisObject
            .   contextScope
            .   edh'context
        __repr__ :: EdhProcedure
        __repr__ _ !exit = exitEdhProc exit $ EdhString $ T.pack $ show he
    writeTVar (entity'store $ objEntity this) $ toDyn he
    methods <- sequence
      [ (AttrByName nm, ) <$> mkHostProc scope vc nm hp args
      | (nm, vc, hp, args) <-
        [ ("__init__", EdhMethod, __init__, WildReceiver)
        , ("__repr__", EdhMethod, __repr__, PackReceiver [])
        ]
      ]
    writeTVar obs $ Map.fromList methods


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


type EdhHostCtor
  =  EdhProgState
  -> ArgsPack -- ctor args, if __init__() is provided, will go there too
  -> TVar (Map.HashMap AttrKey EdhValue)  -- out-of-band attr store
  -> STM ()

mkHostClass
  :: Scope -- ^ outer lexical scope
  -> Text  -- ^ class name
  -> Bool  -- ^ write protect the out-of-band attribute store
  -> EdhHostCtor
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
            ctorScope = Scope { scopeEntity       = ent
                              , thisObject        = newThis
                              , thatObject        = newThis
                              , scopeProc         = cls
                              , scopeCaller       = contextStmt ctx
                              , exceptionHandlers = []
                              }
        hc pgsCtor apk obs
        exitEdhSTM pgs exit $ EdhObject newThis
  return $ EdhClass cls


runEdhProgram :: MonadIO m => Context -> EdhProg -> m (Either EdhError EdhValue)
runEdhProgram !ctx !prog =
  liftIO $ tryJust edhKnownError $ runEdhProgram' ctx prog

runEdhProgram' :: MonadIO m => Context -> EdhProg -> m EdhValue
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

