
module Language.Edh.Runtime where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Exception
import           Control.Monad.Except

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
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.Evaluate


createEdhWorld :: MonadIO m => EdhConsole -> m EdhWorld
createEdhWorld !console = liftIO $ do

  -- * the meta class and root class
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

  -- * the `scope` class
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
  let scopeAllocator !ets (ArgsPack _args !kwargs) !exit =
        case odLookup (AttrByName "ofObj") kwargs of
          Just !val -> case val of
            EdhObject !obj -> case objectScope obj of
              Nothing ->
                throwEdh ets UsageError
                  $  "no scope from a host object of class: "
                  <> objClassName obj
              Just !objScope -> exit =<< HostStore <$> newTVar (toDyn objScope)
            _ -> throwEdh ets UsageError $ "not an object but a " <> T.pack
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

  -- * error classes
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
    [ (AttrByName $ edhClassName clsObj, EdhObject clsObj)
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

  -- * the `module` class
  !hsModuCls <-
    atomically
    $ (iopdFromList =<<)
    $ sequence
    $ [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm mth args
      | (nm, mth, args) <-
        [ ("__repr__", mthModuClsRepr, PackReceiver [])
        , ("__show__", mthModuClsShow, PackReceiver [])
        ]
      ]
  !clsModule <- atomically
    $ mkHostClass rootScope "module" moduleAllocator hsModuCls []
  let edhCreateModule :: ModuleId -> String -> STM Object
      edhCreateModule moduId srcName = do
        !idModu <- unsafeIOToSTM newUnique
        !hs     <- iopdFromList
          [ (AttrByName "__path__", EdhString moduId)
          , (AttrByName "__file__", EdhString $ T.pack srcName)
          ]
        !ss <- newTVar []
        return Object { edh'obj'ident  = idModu
                      , edh'obj'store  = HashStore hs
                      , edh'obj'class  = clsModule
                      , edh'obj'supers = ss
                      }
  atomically $ iopdUpdate [(AttrByName "module", EdhObject clsModule)] hsRoot


  -- * operator precedence dict
  opPD  <- newTMVarIO Map.empty

  -- * the container of loaded modules
  modus <- newTMVarIO Map.empty

  -- assembly the world with pieces prepared above
  let world = EdhWorld { edh'world'root        = rootScope
                       , edh'world'operators   = opPD
                       , edh'world'modules     = modus
                       , edh'world'console     = console
                       , edh'scope'wrapper     = edhWrapScope
                       , edh'exception'wrapper = edhWrapException
                       , edh'module'creator    = edhCreateModule
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
      exitEdhSTM ets exit $ EdhString $ procedureName pd
    _ -> exitEdhSTM ets exit $ EdhString "<bogus-class>"
    where clsObj = edh'scope'this $ contextScope $ edh'context ets

  mthClassNameGetter :: EdhHostProc
  mthClassNameGetter _apk !exit !ets = case edh'obj'store clsObj of
    ClassStore (Class !pd _ _) ->
      exitEdhSTM ets exit $ attrKeyValue $ edh'procedure'name pd
    _ -> exitEdhSTM ets exit nil
    where clsObj = edh'scope'this $ contextScope $ edh'context ets

  mthScopeRepr :: EdhHostProc
  mthScopeRepr _ !exit = exitEdhTx exit $ EdhString "<scope>"

  mthScopeShow :: EdhHostProc
  mthScopeShow _ !exit !ets =
    case edh'obj'store $ edh'scope'this $ contextScope $ edh'context ets of
      HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
        Nothing -> exitEdhSTM ets exit $ EdhString $ "bogus scope object"
        Just (scope :: Scope) -> do
          let !pd      = edh'scope'proc scope
              !pb      = edh'procedure'body $ edh'procedure'decl pd
              !lexiLoc = case pb of
                Left  (StmtSrc (srcLoc, _)) -> T.pack $ sourcePosPretty srcLoc
                Right _                     -> "<host-code>"
              StmtSrc (!callerSrcLoc, _) = edh'scope'caller scope
          exitEdhSTM ets exit
            $  EdhString
            $  "#scope@ "
            <> lexiLoc
            <> "\n#called by: "
            <> T.pack (sourcePosPretty callerSrcLoc)
      _ -> exitEdhSTM ets exit $ EdhString $ "bogus scope object"

  mthScopeOuterGetter :: EdhHostProc
  mthScopeOuterGetter _ !exit !ets = case edh'obj'store this of
    HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
      Nothing -> exitEdhSTM ets exit $ EdhString $ "bogus scope object"
      Just (scope :: Scope) -> do
        let !outerScope = edh'procedure'lexi $ edh'scope'proc scope
        if edh'scope'proc outerScope == edh'scope'proc scope
          then exitEdhSTM ets exit nil
          else do
            !oid  <- unsafeIOToSTM newUnique
            !hsv' <- newTVar $ toDyn outerScope
            !ss   <- newTVar []
            exitEdhSTM ets exit $ EdhObject $ Object oid
                                                     (HostStore hsv')
                                                     (edh'obj'class this)
                                                     ss
    _ -> exitEdhSTM ets exit $ EdhString $ "bogus scope object"
    where !this = edh'scope'this $ contextScope $ edh'context ets

  -- this is called in case a ProgramHalt is constructed by Edh code
  haltAllocator _ !apk !exit = case apk of
    ArgsPack [v] !kwargs | odNull kwargs ->
      exit =<< HostStore <$> newTVar (toDyn $ ProgramHalt $ toDyn v)
    _ -> exit =<< HostStore <$> newTVar
      (toDyn $ ProgramHalt $ toDyn $ EdhArgsPack apk)

  -- creating an IOError from Edh code
  ioErrAllocator !ets apk@(ArgsPack !args !kwargs) !exit = case args of
    [EdhString !m] | odNull kwargs -> createErr $ T.unpack m
    _                              -> edhValueRepr ets (EdhArgsPack apk)
      $ \ !repr -> createErr $ T.unpack repr
   where
    createErr !msg = exit =<< HostStore <$> newTVar
      (toDyn $ EdhIOError $ SomeException $ userError msg)

  -- a peer error is most prolly created from Edh code
  peerErrAllocator _ !apk !exit = exit =<< HostStore <$> newTVar
    (toDyn peerError)
   where
    peerError = case apk of
      (ArgsPack [EdhString !peerSite, EdhString !details] !kwargs)
        | odNull kwargs -> EdhPeerError peerSite details
      _ -> EdhPeerError "<bogus-peer>" $ T.pack $ show apk

  -- creating a tagged Edh error from Edh code
  errAllocator !tag !ets apk@(ArgsPack !args !kwargs) !exit = case args of
    [] | odNull kwargs' -> createErr ""
    [EdhString !m] | odNull kwargs' -> createErr m
    _ -> edhValueRepr ets (EdhArgsPack apk) $ \ !repr -> createErr repr
   where
    createErr msg =
      exit =<< HostStore <$> newTVar (toDyn $ EdhError tag msg cc)
    (!maybeUnwind, !kwargs') = odTakeOut (AttrByName "unwind") kwargs
    !unwind                  = case maybeUnwind of
      Just (EdhDecimal d) -> case decimalToInteger d of
        Just !n -> fromIntegral n
        _       -> 1
      _ -> 1
    !cc = getEdhCallContext unwind ets

  mthErrShow :: EdhHostProc
  mthErrShow _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> readTVar hsv >>= \ !hsd -> case fromDynamic hsd of
      Just (err :: EdhError) ->
        exitEdhSTM ets exit $ EdhString $ T.pack (show err)
      Nothing -> case fromDynamic hsd of
        Just (exc :: SomeException) ->
          exitEdhSTM ets exit $ EdhString $ errClsName <> ": " <> T.pack
            (show exc)
        Nothing ->
          exitEdhSTM ets exit
            $  EdhString
            $  "bogus error object of: "
            <> errClsName
    _ ->
      exitEdhSTM ets exit $ EdhString $ "bogus error object of: " <> errClsName
   where
    !errObj     = edh'scope'this $ contextScope $ edh'context ets
    !errClsName = objClassName errObj

  mthErrRepr :: EdhHostProc
  mthErrRepr _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> readTVar hsv >>= \ !hsd -> case fromDynamic hsd of
      Just (ProgramHalt !dhv) -> case fromDynamic dhv of
        Just (val :: EdhValue) -> edhValueRepr ets val $ \ !repr ->
          exitEdhSTM ets exit $ EdhString $ errClsName <> "(" <> repr <> ")"
        Nothing -> exitEdhSTM ets exit $ EdhString $ errClsName <> "()"
      Just (EdhIOError !exc) ->
        exitEdhSTM ets exit
          $  EdhString
          $  errClsName
          <> "("
          <> T.pack (show $ show exc)
          <> ")"
      Just (EdhPeerError !peerSite !details) ->
        exitEdhSTM ets exit
          $  EdhString
          $  errClsName
          <> "("
          <> T.pack (show peerSite)
          <> ","
          <> T.pack (show details)
          <> ")"
      Just (EdhError _tag !msg _cc) -> if T.null msg
        then exitEdhSTM ets exit $ EdhString $ errClsName <> "()"
        else exitEdhSTM ets exit $ EdhString $ errClsName <> "(`" <> msg <> "`)"
      _ -> exitEdhSTM ets exit $ EdhString $ errClsName <> "()"
    _ -> exitEdhSTM ets exit $ EdhString $ errClsName <> "()"
   where
    !errObj     = edh'scope'this $ contextScope $ edh'context ets
    !errClsName = objClassName errObj

  mthErrStackGetter :: EdhHostProc
  mthErrStackGetter _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
      Just (EdhError _errTag _errMsg (EdhCallContext !tip !frames)) ->
        exitEdhSTM ets exit $ EdhArgsPack $ ArgsPack
          (EdhString . dispEdhCallFrame <$> frames)
          (odFromList [(AttrByName "tip", EdhString tip)])
      _ -> exitEdhSTM ets exit nil
    _ -> exitEdhSTM ets exit nil
    where errObj = edh'scope'this $ contextScope $ edh'context ets

  moduleAllocator :: EdhObjectAllocator
  moduleAllocator !ets !apk !exit = case apk of
    (ArgsPack [moduId] !kwargs) | odNull kwargs ->
      exit =<< HashStore <$> iopdFromList
        [ (AttrByName "__path__", moduId)
        , (AttrByName "__file__", EdhString "<on-the-fly>")
        ]
    _ -> throwEdh ets UsageError "invalid args to module()"

  mthModuClsRepr :: EdhHostProc
  mthModuClsRepr _ !exit !ets = do
    !path <- lookupEdhSelfAttr this (AttrByName "__path__")
    edhValueStr ets path $ \ !pathStr ->
      exitEdhSTM ets exit $ EdhString $ "<module: " <> pathStr <> ">"
    where !this = edh'scope'this $ contextScope $ edh'context ets

  mthModuClsShow :: EdhHostProc
  mthModuClsShow _ !exit !ets = do
    !path <- lookupEdhSelfAttr this (AttrByName "__path__")
    !file <- lookupEdhSelfAttr this (AttrByName "__file__")
    edhValueStr ets path $ \ !pathStr -> edhValueStr ets file $ \ !fileStr ->
      exitEdhSTM ets exit
        $  EdhString
        $  " ** module: "
        <> pathStr
        <> "\n  * loaded from: "
        <> fileStr
    where !this = edh'scope'this $ contextScope $ edh'context ets


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
  !wops = edh'world'operators world
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


haltEdhProgram :: EdhThreadState -> EdhValue -> STM ()
haltEdhProgram !ets !hv =
  edhWrapException (toException $ ProgramHalt $ toDyn hv)
    >>= \ !exo -> edhThrow ets $ EdhObject exo
 where
  !edhWrapException = edh'exception'wrapper (edh'ctx'world $ edh'context ets)


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
  liftIO $ atomically $ edh'module'creator world moduId srcName


type EdhModulePreparation = EdhThreadState -> STM () -> STM ()
edhModuleAsIs :: EdhModulePreparation
edhModuleAsIs _ets !exit = exit


installEdhModule
  :: MonadIO m => EdhWorld -> ModuleId -> EdhModulePreparation -> m Object
installEdhModule !world !moduId !preInstall = liftIO $ do
  modu <- createEdhModule world moduId "<host-code>"
  void $ runEdhProgram' (worldContext world) $ \ !ets -> do
    let !moduCtx = moduleContext world modu
        !etsModu = ets { edh'context = moduCtx }
    preInstall etsModu $ do
      moduSlot <- newTMVar $ EdhObject modu
      moduMap  <- takeTMVar (edh'world'modules world)
      putTMVar (edh'world'modules world) $ Map.insert moduId moduSlot moduMap
  return modu

installedEdhModule :: MonadIO m => EdhWorld -> ModuleId -> m (Maybe Object)
installedEdhModule !world !moduId =
  liftIO $ atomically $ tryReadTMVar (edh'world'modules world) >>= \case
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
    Some !moduSource _ _ -> runEdhProgram' (worldContext world) $ \ !ets -> do
      let !moduId = T.pack nomPath
      !modu <- edh'module'creator world moduId moduFile
      let !moduCtx = moduleContext world modu
          !etsModu = ets { edh'context = moduCtx }
      preRun etsModu $ runEdhTx etsModu $ evalEdh moduFile moduSource endOfEdh


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
performEdhEffect !effKey !args !kwargs !exit !ets =
  resolveEdhPerform ets effKey $ \ !effVal ->
    edhPrepareCall'
        ets
        effVal
        (ArgsPack args $ odFromList $ [ (AttrByName k, v) | (k, v) <- kwargs ])
      $ \ !mkCall -> runEdhTx ets $ mkCall exit

-- | obtain an effectful value from current Edh context
--
-- if performing from an effectful procedure call, use the outer stack of
-- that call in effect resolution
--
-- otherwise this is the same as 'behaveEdhEffect''
performEdhEffect' :: AttrKey -> (EdhValue -> EdhTx) -> EdhTx
performEdhEffect' !effKey !exit !ets =
  resolveEdhPerform ets effKey $ runEdhTx ets . exit


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
behaveEdhEffect !effKey !args !kwargs !exit !ets =
  resolveEdhBehave ets effKey $ \ !effVal ->
    edhPrepareCall'
        ets
        effVal
        (ArgsPack args $ odFromList $ [ (AttrByName k, v) | (k, v) <- kwargs ])
      $ \ !mkCall -> runEdhTx ets $ mkCall exit

-- | obtain an effectful value from current Edh context
--
-- use full stack in effect resolution
behaveEdhEffect' :: AttrKey -> (EdhValue -> EdhTx) -> EdhTx
behaveEdhEffect' !effKey !exit !ets =
  resolveEdhBehave ets effKey $ runEdhTx ets . exit

