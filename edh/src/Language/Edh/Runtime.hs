
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
  !idMeta <- newUnique
  !hsMeta <- atomically iopdEmpty
  !ssMeta <- newTVarIO []

  !idRoot <- newUnique
  !hsRoot <- atomically $ iopdFromList
    [(AttrByName "None", edhNone), (AttrByName "Nothing", edhNothing)]
  !ssRoot <- newTVarIO []

  let
    metaProc = ProcDefi idMeta (AttrByName "class") rootScope
      $ ProcDecl (NamedAttr "class") (PackReceiver []) (Right fakeHostProc)
    metaClass    = Class metaProc hsMeta rootAllocator
    metaClassObj = Object idMeta (ClassStore metaClass) metaClassObj ssMeta

    rootProc     = ProcDefi idRoot (AttrByName "<root>") rootScope
      $ ProcDecl (NamedAttr "<root>") (PackReceiver []) (Right fakeHostProc)
    rootClass    = Class rootProc hsRoot rootAllocator
    rootClassObj = Object idRoot (ClassStore rootClass) metaClassObj ssRoot

    rootObj      = Object idRoot (HashStore hsRoot) rootClassObj ssRoot

    rootScope =
      Scope hsRoot rootObj rootObj defaultEdhExcptHndlr rootProc genesisStmt []

  atomically
    $  (flip iopdUpdate hsMeta =<<)
    $  sequence
    -- todo more static attrs for class objects here
    $  [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm mth args
       | (nm, mth, args) <- [("__repr__", mthClassRepr, PackReceiver [])]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty rootScope nm getter setter
       | (nm, getter, setter) <- [("name", mthClassNameGetter, Nothing)]
       ]

  !hsScope <- -- TODO port eval/get/put/attrs methods
    atomically
    $  (iopdFromList =<<)
    $  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm mth args
       | (nm, mth, args) <-
         [ ("__repr__", mthScopeRepr, PackReceiver [])
         , ("__show__", mthScopeShow, PackReceiver [])
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty rootScope nm getter setter
       | (nm, getter, setter) <- [("outer", mthScopeOuterGetter, Nothing)]
       ]
  let
    scopeAllocator !ets (ArgsPack _args !kwargs) !exit =
      case odLookup (AttrByName "ofObj") kwargs of
        Just !val -> case val of
          EdhObject !obj -> objectScope obj
            $ \ !objScope -> exit =<< HostStore <$> newTVar (toDyn objScope)
          _ -> throwEdhSTM ets UsageError $ "not an object but a " <> T.pack
            (edhTypeNameOf val)
        Nothing -> exit =<< HostStore <$> newTVar
          (toDyn $ contextScope $ edh'context ets)
  !clsScope <- atomically
    $ mkHostClass rootScope "scope" scopeAllocator hsScope []
  let edhWrapScope :: Scope -> STM Object
      edhWrapScope !scope = do
        !idScope <- unsafeIOToSTM newUnique
        !hs      <- newTVar $ toDyn scope
        !ss      <- newTVar []
        return Object { edh'obj'ident  = idScope
                      , edh'obj'store  = HostStore hs
                      , edh'obj'class  = clsScope
                      , edh'obj'supers = ss
                      }
  atomically $ iopdUpdate [(AttrByName "scope", EdhObject clsScope)] hsRoot

  !hsErrCls <-
    atomically
    $  (iopdFromList =<<)
    $  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm mth args
       | (nm, mth, args) <-
         [ ("__repr__", mthErrRepr, PackReceiver [])
         , ("__show__", mthErrShow, PackReceiver [])
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty rootScope nm getter setter
       | (nm, getter, setter) <- [("stack", mthErrStackGetter, Nothing)]
       ]
  clsProgramHalt <- atomically
    $ mkHostClass rootScope "ProgramHalt" haltAllocator hsErrCls []
  clsIOError <- atomically
    $ mkHostClass rootScope "IOError" ioErrAllocator hsErrCls []
  clsPeerError <- atomically
    $ mkHostClass rootScope "PeerError" peerErrAllocator hsErrCls []
  clsException <- atomically
    $ mkHostClass rootScope "Exception" (errAllocator EdhException) hsErrCls []
  clsPackageError <- atomically $ mkHostClass rootScope
                                              "PackageError"
                                              (errAllocator PackageError)
                                              hsErrCls
                                              []
  clsParseError <- atomically
    $ mkHostClass rootScope "ParseError" (errAllocator ParseError) hsErrCls []
  clsEvalError <- atomically
    $ mkHostClass rootScope "EvalError" (errAllocator EvalError) hsErrCls []
  clsUsageError <- atomically
    $ mkHostClass rootScope "UsageError" (errAllocator UsageError) hsErrCls []

  let edhWrapException :: SomeException -> STM Object
      edhWrapException !exc = do
        !uidErr    <- unsafeIOToSTM newUnique
        !supersErr <- newTVar []
        case edhKnownError exc of
          Just !err -> do
            !hsv <- newTVar $ toDyn err
            let !clsErr = case err of
                  ProgramHalt{}    -> clsProgramHalt
                  EdhIOError{}     -> clsIOError
                  EdhPeerError{}   -> clsPeerError
                  EdhError !et _ _ -> case et of
                    EdhException -> clsException
                    PackageError -> clsPackageError
                    ParseError   -> clsParseError
                    EvalError    -> clsEvalError
                    UsageError   -> clsUsageError
            return $ Object uidErr (HostStore hsv) clsErr supersErr
          Nothing -> do
            !hsv <- newTVar $ toDyn $ EdhIOError exc
            return $ Object uidErr (HostStore hsv) clsIOError supersErr

  atomically $ iopdUpdate
    [ (AttrByName (className clsObj), EdhObject clsObj)
    | clsObj <-
      [ clsProgramHalt
      , clsIOError
      , clsPeerError
      , clsException
      , clsPackageError
      , clsParseError
      , clsEvalError
      , clsUsageError
      ]
    ]
    hsRoot

  -- operator precedence dict
  opPD  <- newTMVarIO Map.empty

  -- the container of loaded modules
  modus <- newTMVarIO Map.empty

  -- assembly the world with pieces prepared above
  let world = EdhWorld { edh'world'root        = rootScope
                       , edh'world'operators   = opPD
                       , edh'world'modules     = modus
                       , edh'world'console     = console
                       , edh'scope'wrapper     = edhWrapScope
                       , edh'exception'wrapper = edhWrapException
                       }

  return world
 where
  fakeHostProc :: EdhHostProc
  fakeHostProc _ !exit = exitEdhTx exit nil

  genesisStmt :: StmtSrc
  genesisStmt = StmtSrc
    ( SourcePos { sourceName   = "<genesis>"
                , sourceLine   = mkPos 1
                , sourceColumn = mkPos 1
                }
    , VoidStmt
    )

  rootAllocator _ _ _ = error "bug: allocating root object"

  mthClassRepr :: EdhHostProc
  mthClassRepr _apk !exit !ets = case edh'obj'store clsObj of
    ClassStore (Class !pd _ _) ->
      exitEdh ets exit $ EdhString $ procedureName pd
    _ -> exitEdh ets exit $ EdhString "<bogus-class>"
    where clsObj = edh'scope'this $ contextScope $ edh'context ets

  mthClassNameGetter :: EdhHostProc
  mthClassNameGetter _apk !exit !ets = case edh'obj'store clsObj of
    ClassStore (Class !pd _ _) ->
      exitEdh ets exit $ attrKeyValue $ edh'procedure'name pd
    _ -> exitEdh ets exit nil
    where clsObj = edh'scope'this $ contextScope $ edh'context ets

  mthScopeRepr :: EdhHostProc
  mthScopeRepr _ !exit _ = exitEdh exit $ EdhString "<scope>"

  mthScopeShow :: EdhHostProc
  mthScopeShow _ !exit !ets =
    case edh'obj'store $ edh'scope'this $ contextScope $ edh'context ets of
      HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
        Just (scope :: Scope) -> do
          let !pd      = edh'scope'proc scope
              !pb      = edh'procedure'body $ edh'procedure'decl pd
              !lexiLoc = case pb of
                Left  (StmtSrc (srcLoc, _)) -> T.pack $ sourcePosPretty srcLoc
                Right _                     -> "<host-code>"
              StmtSrc (!callerSrcLoc, _) = edh'scope'caller scope
          exitEdh ets exit
            $  EdhString
            $  "#scope@ "
            <> lexiLoc
            <> "\n#called by: " T.pack (sourcePosPretty callerSrcLoc)
        Nothing -> exitEdh ets exit $ EdhString $ "bogus scope object"
      _ -> exitEdh ets exit $ EdhString $ "bogus scope object"

  mthScopeOuterGetter :: EdhHostProc
  mthScopeOuterGetter _ !exit !ets = case edh'obj'store this of
    HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
      Just (scope :: Scope) -> do
        let !outerScope = edh'procedure'lexi $ edh'scope'proc scope
        if edh'scope'proc outerScope == edh'scope'proc scope
          then exitEdh ets exit nil
          else do
            !oid  <- unsafeIOToSTM newUnique
            !hsv' <- newTVar $ toDyn outerScope
            !ss   <- newTVar []
            exitEdh ets exit $ EdhObject $ Object oid
                                                  (HostStore hsv')
                                                  (edh'obj'class this)
                                                  ss
    where !this = edh'scope'this $ contextScope $ edh'context ets

  -- this is called in case a ProgramHalt is constructed by Edh code
  haltAllocator _ !apk !exit = case apk of
    ArgsPack [v] !kwargs | odNull kwargs ->
      exit =<< HostStore <$> newTVar (toDyn $ ProgramHalt $ toDyn v)
    _ -> exit =<< HostStore <$> newTVar
      (toDyn $ ProgramHalt $ toDyn $ EdhArgsPack apk)

  -- creating an IOError from Edh code
  ioErrAllocator _ apk@(ArgsPack !args !kwargs) !exit =
    exit =<< HostStore <$> newTVar
      (toDyn $ EdhIOError $ SomeException $ userError msg)
   where
    !msg = case args of
      [EdhString !msg] | odNull kwargs -> T.unpack msg
      -- TODO use apk's repr once edhValueRepr works
      _ -> show apk

  -- a peer error is most prolly created from Edh code
  peerErrAllocator _ !apk !exit = exit =<< HostStore <$> newTVar
    (toDyn peerError)
   where
    peerError = case apk of
      (ArgsPack [EdhString !peerSite, EdhString !details] !kwargs)
        | odNull kwargs -> EdhPeerError peerSite details
      _ -> EdhPeerError "<bogus-peer>" $ T.pack $ show apk

  -- creating a tagged Edh error from Edh code
  errAllocator !tag !ets apk@(ArgsPack !args !kwargs) !exit =
    exit =<< HostStore <$> newTVar (toDyn $ EdhError et msg cc)
   where
    (!maybeUnwind, !kwargs') = odTakeOut (AttrByName "unwind") kwargs
    !unwind                  = case maybeUnwind of
      Just (EdhDecimal d) -> case decimalToInteger d of
        Just !n -> fromIntegral n
        _       -> 1
      _ -> 1
    !cc  = getEdhCallContext unwind ets
    !msg = case args of
      [] | odNull kwargs' -> ""
      [EdhString !msg] | odNull kwargs' -> msg
      -- TODO use apk's repr once edhValueRepr works
      _                   -> T.pack (show $ ArgsPack args kwargs')

  mthErrShow :: EdhHostProc
  mthErrShow _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> readTVar hsv >>= \ !hsd -> case fromDynamic hsd of
      Just (err :: EdhError) ->
        exitEdh ets exit $ EdhString $ T.pack (show err)
      Nothing -> case hsd of
        Just (exc :: SomeException) ->
          exitEdh ets exit $ EdhString $ errClsName <> ": " <> T.pack (show exc)
        Nothing ->
          exitEdh ets exit $ EdhString $ "bogus error object of: " <> errClsName
    _ -> exitEdh ets exit $ EdhString $ "bogus error object of: " <> errClsName

  mthErrRepr :: EdhHostProc
  mthErrRepr _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
      ProgramHalt !dhv -> case fromDynamic dhv of
        -- TODO use repr of val once edhValueRepr works
        (val :: EdhValue) ->
          exitEdh ets exit
            $  EdhString
            $  errClsName
            <> "("
            <> T.pack (show val)
            <> ")"
        _ -> exitEdh ets exit $ EdhString $ errClsName <> "()"
      EdhIOError !exc ->
        exitEdh ets exit
          $  EdhString
          $  errClsName
          <> "("
          <> T.pack (show $ show exc)
          <> ")"
      EdhPeerError !peerSite !details ->
        -- TODO use repr of peerSite/details once edhValueRepr works
        exitEdh ets exit
          $  EdhString
          $  errClsName
          <> "("
          <> T.pack (show peerSite)
          <> ","
          <> T.pack (show details)
          <> ")"
      EdhError _tag !msg _cc -> if T.null msg
        then exitEdh ets exit $ EdhString $ errClsName <> "()"
        else exitEdh ets exit $ EdhString $ errClsName <> "(`" <> msg <> "`)"
      _ -> exitEdh ets exit $ EdhString $ errClsName <> "()"
    _ -> exitEdh ets exit $ EdhString $ errClsName <> "()"
   where
    !errObj     = edh'scope'this $ contextScope $ edh'context ets
    !errClsName = objClassName errObj

  mthErrStackGetter :: EdhHostProc
  mthErrStackGetter _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
      Just (EdhError _errTag _errMsg (EdhCallContext !tip !frames)) ->
        exitEdh ets exit $ EdhArgsPack $ ArgsPack
          (EdhString . dispEdhCallFrame <$> frames)
          (odFromList [(AttrByName "tip", EdhString tip)])
      _ -> exitEdh ets exit nil
    _ -> exitEdh ets exit nil
    where errObj = edh'scope'this $ contextScope $ edh'context ets


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


runEdhProgram :: MonadIO m => Context -> EdhTx -> m (Either EdhError EdhValue)
runEdhProgram !ctx !prog =
  liftIO $ tryJust edhKnownError $ runEdhProgram' ctx prog

runEdhProgram' :: MonadIO m => Context -> EdhTx -> m EdhValue
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
        preRun pgsModu $ runEdhTx pgsModu $ evalEdh moduFile moduSource endOfEdh


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
  -> (EdhValue -> EdhTx)
  -> EdhTx
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
          $ \mkCall -> runEdhTx pgs $ mkCall $ \(OriginalValue !rtnVal _ _) ->
              exit rtnVal

-- | obtain an effectful value from current Edh context
--
-- if performing from an effectful procedure call, use the outer stack of
-- that call in effect resolution
--
-- otherwise this is the same as 'behaveEdhEffect''
performEdhEffect' :: AttrKey -> (EdhValue -> EdhTx) -> EdhTx
performEdhEffect' !effKey !exit = ask >>= \ !pgs ->
  contEdhSTM $ resolveEdhPerform pgs effKey $ runEdhTx pgs . exit


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
  -> (EdhValue -> EdhTx)
  -> EdhTx
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
          $ \mkCall -> runEdhTx pgs $ mkCall $ \(OriginalValue !rtnVal _ _) ->
              exit rtnVal

-- | obtain an effectful value from current Edh context
--
-- use full stack in effect resolution
behaveEdhEffect' :: AttrKey -> (EdhValue -> EdhTx) -> EdhTx
behaveEdhEffect' !effKey !exit = ask
  >>= \ !pgs -> contEdhSTM $ resolveEdhBehave pgs effKey $ runEdhTx pgs . exit

