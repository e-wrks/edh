
module Language.Edh.Runtime where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Exception
import           Control.Monad.Except

import           Control.Concurrent.STM

import           Data.Maybe
import qualified Data.List.NonEmpty            as NE
import qualified Data.ByteString               as B
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Text.Encoding
import           Data.Text.Encoding.Error
import qualified Data.HashMap.Strict           as Map
import           Data.Unique
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

  -- * the meta class and namespace class
  !idMeta      <- newUnique
  !hsMeta      <- atomically iopdEmpty
  !ssMeta      <- newTVarIO []

  !idNamespace <- newUnique
  !hsNamespace <- atomically iopdEmpty
  !ssNamespace <- newTVarIO []

  -- root object is an instance of namespace class per se
  !idRoot      <- newUnique
  !hsRoot      <- atomically $ iopdFromList
    [ (AttrByName "__name__", EdhString "<root>")
    , (AttrByName "None"    , edhNone)
    , (AttrByName "Nothing" , edhNothing)
    , (AttrByName "NA"      , edhNA)
    ]
  !ssRoot <- newTVarIO []

  let
    metaProc = ProcDefi idMeta (AttrByName "class") rootScope
      $ ProcDecl (NamedAttr "class") (PackReceiver []) (Right phantomHostProc)
    metaClass    = Class metaProc hsMeta phantomAllocator
    metaClassObj = Object idMeta (ClassStore metaClass) metaClassObj ssMeta

    nsProc       = ProcDefi idNamespace (AttrByName "namespace") rootScope
      $ ProcDecl
          (NamedAttr "namespace")
          (PackReceiver [])
          (Right phantomHostProc)
    nsClass = Class nsProc hsNamespace phantomAllocator
    nsClassObj =
      Object idNamespace (ClassStore nsClass) metaClassObj ssNamespace

    rootObj = Object idRoot (HashStore hsRoot) nsClassObj ssRoot

    rootScope =
      Scope hsRoot rootObj rootObj defaultEdhExcptHndlr nsProc genesisStmt []

  atomically
    $  (flip iopdUpdate hsMeta =<<)
    $  sequence
    -- todo more static attrs for class objects here
    $  [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm mth args
       | (nm, mth, args) <-
         [ ("__repr__", mthClassRepr, PackReceiver [])
         , ("__show__", mthClassShow, PackReceiver [])
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty rootScope nm getter setter
       | (nm, getter, setter) <- [("name", mthClassNameGetter, Nothing)]
       ]

  atomically
    $ (flip iopdUpdate hsNamespace =<<)
    $ sequence
    $ [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm mth args
      | (nm, mth, args) <-
        [ ("__repr__", mthNsRepr, PackReceiver [])
        , ("__show__", mthNsShow, PackReceiver [])
        , ("__desc__", mthNsDesc, PackReceiver [])
        ]
      ]

  atomically
    $ iopdUpdate [(AttrByName "namespace", EdhObject nsClassObj)] hsRoot

  -- * the `scope` class
  !hsScope <- -- TODO port eval/get/put/attrs methods
    atomically
    $  (iopdFromList =<<)
    $  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm mth args
       | (nm, mth, args) <-
         [ ("__repr__", mthScopeRepr , PackReceiver [])
         , ("__show__", mthScopeShow , PackReceiver [])
         , ("eval"    , mthScopeEval , PackReceiver [])
         , ("get"     , mthScopeGet  , PackReceiver [])
         , ("put"     , mthScopePut  , PackReceiver [])
         , ("attrs"   , mthScopeAttrs, PackReceiver [])
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty rootScope nm getter setter
       | (nm, getter, setter) <-
         [ ("lexiLoc"  , mthScopeLexiLoc  , Nothing)
         , ("callerLoc", mthScopeCallerLoc, Nothing)
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
         , ("__desc__", mthErrDesc, PackReceiver [])
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty rootScope nm getter setter
       | (nm, getter, setter) <-
         [ ("stack"  , mthErrStackGetter  , Nothing)
         , ("message", mthErrMsgGetter    , Nothing)
         , ("details", mthErrDetailsGetter, Nothing)
         ]
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
            !hsv <- newTVar $ toDyn $ toException err
            let !clsErr = case err of
                  ProgramHalt{}      -> clsProgramHalt
                  EdhIOError{}       -> clsIOError
                  EdhPeerError{}     -> clsPeerError
                  EdhError !et _ _ _ -> case et of
                    EdhException -> clsException
                    PackageError -> clsPackageError
                    ParseError   -> clsParseError
                    EvalError    -> clsEvalError
                    UsageError   -> clsUsageError
            return $ Object uidErr (HostStore hsv) clsErr supersErr
          Nothing -> do
            !hsv <- newTVar $ toDyn $ toException $ EdhIOError exc
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

  phantomAllocator _ _ _ = error "bug: allocating phantom object"
  phantomHostProc :: EdhHostProc
  phantomHostProc _ _ = throwEdhTx EvalError "bug: calling phantom procedure"

  genesisStmt :: StmtSrc
  genesisStmt = StmtSrc
    ( SourcePos { sourceName   = "<genesis>"
                , sourceLine   = mkPos 1
                , sourceColumn = mkPos 1
                }
    , VoidStmt
    )


  mthClassRepr :: EdhHostProc
  mthClassRepr _apk !exit !ets = case edh'obj'store clsObj of
    ClassStore (Class !pd _ _) ->
      exitEdh ets exit $ EdhString $ procedureName pd
    _ -> exitEdh ets exit $ EdhString "<bogus-class>"
    where !clsObj = edh'scope'that $ contextScope $ edh'context ets

  mthClassShow :: EdhHostProc
  mthClassShow _apk !exit !ets = case edh'obj'store clsObj of
    ClassStore (Class !pd _ _) ->
      exitEdh ets exit $ EdhString $ "class: " <> procedureName pd
    _ -> exitEdh ets exit $ EdhString "<bogus-class>"
    where !clsObj = edh'scope'that $ contextScope $ edh'context ets

  mthClassNameGetter :: EdhHostProc
  mthClassNameGetter _apk !exit !ets = case edh'obj'store clsObj of
    ClassStore (Class !pd _ _) ->
      exitEdh ets exit $ attrKeyValue $ edh'procedure'name pd
    _ -> exitEdh ets exit nil
    where clsObj = edh'scope'that $ contextScope $ edh'context ets



  mthNsRepr :: EdhHostProc
  mthNsRepr _apk !exit !ets = exitEdh ets exit . EdhString =<< nsRepr
   where
    !scope = contextScope $ edh'context ets
    nsRepr :: STM Text
    nsRepr = case edh'obj'store $ edh'scope'this scope of
      HashStore !hs -> iopdLookup (AttrByName "__name__") hs >>= \case
        Just (EdhString !nsn) -> return $ "<namespace: " <> nsn <> ">"
        Just (EdhSymbol (Symbol _ !nssr)) ->
          return $ "<namespace: " <> nssr <> ">"
        Nothing -> return "<namespace>"
        _       -> return "<bogus-namespace>"
      _ -> return "<bogus-namespace>"

  mthNsShow :: EdhHostProc
  mthNsShow _apk !exit !ets = exitEdh ets exit . EdhString =<< nsShow
   where
    !scope = contextScope $ edh'context ets
    nsShow :: STM Text
    nsShow = case edh'obj'store $ edh'scope'this scope of
      HashStore !hs -> iopdLookup (AttrByName "__name__") hs >>= \case
        Just (EdhString !nsn) ->
          return $ "It's a namespace named `" <> nsn <> "`"
        Just (EdhSymbol (Symbol _ !nssr)) ->
          return $ "It's a symbolic namespace named `" <> nssr <> "`"
        Nothing -> return "It's an anonymous namespace"
        _       -> return "It's a bogus-namespace"
      _ -> return "It's a bogus-namespace"

  mthNsDesc :: EdhHostProc
  mthNsDesc _apk !exit !ets = exitEdh ets exit . EdhString =<< nsDesc
   where
    !scope = contextScope $ edh'context ets
    nsDesc :: STM Text
    -- TODO elaborate the informatiion
    nsDesc = case edh'obj'store $ edh'scope'this scope of
      HashStore !hs -> iopdLookup (AttrByName "__name__") hs >>= \case
        Just (EdhString !nsn) ->
          return $ "It's a namespace named `" <> nsn <> "`"
        Just (EdhSymbol (Symbol _ !nssr)) ->
          return $ "It's a symbolic namespace named `" <> nssr <> "`"
        Nothing -> return "It's an anonymous namespace"
        _       -> return "It's a bogus-namespace"
      _ -> return "It's a bogus-namespace"


  mthScopeRepr :: EdhHostProc
  mthScopeRepr _ !exit = exitEdhTx exit $ EdhString "<scope>"

  mthScopeShow :: EdhHostProc
  mthScopeShow _ !exit !ets =
    castObjectStore (edh'scope'this $ contextScope $ edh'context ets) >>= \case
      Nothing               -> exitEdh ets exit $ EdhString "bogus scope object"
      Just (scope :: Scope) -> scopeLexiLoc scope $ \ !lexiLoc -> do
        let StmtSrc (!callerSrcLoc, _) = edh'scope'caller scope
        exitEdh ets exit
          $  EdhString
          $  "#scope@ "
          <> lexiLoc
          <> "\n#called by: "
          <> T.pack (sourcePosPretty callerSrcLoc)

  mthScopeCallerLoc :: EdhHostProc
  mthScopeCallerLoc _ !exit !ets =
    castObjectStore (edh'scope'this $ contextScope $ edh'context ets) >>= \case
      Nothing -> exitEdh ets exit $ EdhString "<bogus scope object>"
      Just (scope :: Scope) -> do
        let StmtSrc (!callerSrcLoc, _) = edh'scope'caller scope
        exitEdh ets exit $ EdhString $ T.pack (sourcePosPretty callerSrcLoc)

  mthScopeLexiLoc :: EdhHostProc
  mthScopeLexiLoc _ !exit !ets =
    castObjectStore (edh'scope'this $ contextScope $ edh'context ets) >>= \case
      Nothing -> exitEdh ets exit $ EdhString "<bogus scope object>"
      Just (scope :: Scope) ->
        scopeLexiLoc scope $ \ !lexiLoc -> exitEdh ets exit $ EdhString lexiLoc

  mthScopeAttrs :: EdhHostProc
  mthScopeAttrs _apk !exit !ets =
    castObjectStore (edh'scope'this $ contextScope $ edh'context ets) >>= \case
      Nothing -> throwEdh ets EvalError "bogus scope object"
      Just (scope :: Scope) ->
        (iopdSnapshot (edh'scope'entity scope) >>=)
          $ exitEdh ets exit
          . EdhArgsPack
          . ArgsPack []

  mthScopeGet :: EdhHostProc
  mthScopeGet (ArgsPack !args !kwargs) !exit !ets =
    castObjectStore (edh'scope'this $ contextScope $ edh'context ets) >>= \case
      Nothing               -> throwEdh ets EvalError "bogus scope object"
      Just (scope :: Scope) -> do
        let !es = edh'scope'entity scope
            lookupAttrs
              :: [EdhValue]
              -> [(AttrKey, EdhValue)]
              -> [EdhValue]
              -> [(AttrKey, EdhValue)]
              -> (([EdhValue], [(AttrKey, EdhValue)]) -> STM ())
              -> STM ()
            lookupAttrs rtnArgs rtnKwArgs [] [] !exit' =
              exit' (rtnArgs, rtnKwArgs)
            lookupAttrs rtnArgs rtnKwArgs [] ((n, v) : restKwArgs) !exit' =
              attrKeyFrom v $ \ !k -> do
                !attrVal <- fromMaybe nil <$> iopdLookup k es
                lookupAttrs rtnArgs
                            ((n, attrVal) : rtnKwArgs)
                            []
                            restKwArgs
                            exit'
            lookupAttrs rtnArgs rtnKwArgs (v : restArgs) kwargs' !exit' =
              attrKeyFrom v $ \ !k -> do
                !attrVal <- fromMaybe nil <$> iopdLookup k es
                lookupAttrs (attrVal : rtnArgs) rtnKwArgs restArgs kwargs' exit'
        lookupAttrs [] [] args (odToList kwargs) $ \case
          ([v]    , []       ) -> exitEdh ets exit v
          (rtnArgs, rtnKwArgs) -> exitEdh ets exit $ EdhArgsPack $ ArgsPack
            (reverse rtnArgs)
            (odFromList rtnKwArgs)
   where
    attrKeyFrom :: EdhValue -> (AttrKey -> STM ()) -> STM ()
    attrKeyFrom (EdhString attrName) !exit' = exit' $ AttrByName attrName
    attrKeyFrom (EdhSymbol sym     ) !exit' = exit' $ AttrBySym sym
    attrKeyFrom badVal _ =
      throwEdh ets UsageError $ "invalid attribute reference type - " <> T.pack
        (edhTypeNameOf badVal)

  mthScopePut :: EdhHostProc
  mthScopePut (ArgsPack !args !kwargs) !exit !ets =
    castObjectStore (edh'scope'this $ contextScope $ edh'context ets) >>= \case
      Nothing               -> throwEdh ets EvalError "bogus scope object"
      Just (scope :: Scope) -> do
        let !es = edh'scope'entity scope
            putAttrs
              :: [EdhValue]
              -> [(AttrKey, EdhValue)]
              -> ([(AttrKey, EdhValue)] -> STM ())
              -> STM ()
            putAttrs []           cumu !exit' = exit' cumu
            putAttrs (arg : rest) cumu !exit' = case arg of
              EdhPair (EdhString !k) !v ->
                putAttrs rest ((AttrByName k, v) : cumu) exit'
              EdhPair (EdhSymbol !k) !v ->
                putAttrs rest ((AttrBySym k, v) : cumu) exit'
              _ ->
                throwEdh ets UsageError
                  $  "invalid key/value type to put into a scope - "
                  <> T.pack (edhTypeNameOf arg)
        putAttrs args [] $ \ !attrs -> do
          iopdUpdate (attrs ++ odToList kwargs) es
          exitEdh ets exit nil

  mthScopeEval :: EdhHostProc
  mthScopeEval (ArgsPack !args !kwargs) !exit !ets =
    castObjectStore (edh'scope'this $ contextScope $ edh'context ets) >>= \case
      Nothing               -> throwEdh ets EvalError "bogus scope object"
      Just (scope :: Scope) -> do
        -- eval all exprs with the original scope on top of current call stack
        let !ctx            = edh'context ets
            !scopeCallStack = scope NE.<| edh'ctx'stack ctx
            !etsEval        = ets
              { edh'context = ctx { edh'ctx'stack        = scopeCallStack
                                  , edh'ctx'genr'caller  = Nothing
                                  , edh'ctx'match        = true
                                  , edh'ctx'pure         = False
                                  , edh'ctx'exporting    = False
                                  , edh'ctx'eff'defining = False
                                  }
              }
        !kwIOPD <- iopdEmpty
        let
          evalThePack
            :: [EdhValue] -> [EdhValue] -> [(AttrKey, EdhValue)] -> STM ()
          evalThePack !argsValues [] [] =
            iopdToList kwIOPD >>= \ !kwargsValues ->
              -- restore original tx state and return the eval-ed values
              exitEdh ets exit $ case argsValues of
                [val] | null kwargsValues -> val
                _ -> EdhArgsPack $ ArgsPack (reverse argsValues) $ odFromList
                  kwargsValues
          evalThePack !argsValues [] (kwExpr : kwargsExprs') = case kwExpr of
            (!kw, EdhExpr _ !expr _) ->
              runEdhTx etsEval $ evalExpr expr $ \ !val _ets -> do
                edhSetValue kw (edhDeCaseClose val) kwIOPD
                evalThePack argsValues [] kwargsExprs'
            !v -> throwEdh ets EvalError $ "not an expr: " <> T.pack (show v)
          evalThePack !argsValues (argExpr : argsExprs') !kwargsExprs =
            case argExpr of
              EdhExpr _ !expr _ ->
                runEdhTx etsEval $ evalExpr expr $ \ !val _ets -> evalThePack
                  (edhDeCaseClose val : argsValues)
                  argsExprs'
                  kwargsExprs
              !v -> throwEdh ets EvalError $ "not an expr: " <> T.pack (show v)
        evalThePack [] args $ odToList kwargs

  mthScopeOuterGetter :: EdhHostProc
  mthScopeOuterGetter _ !exit !ets = case edh'obj'store this of
    HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
      Nothing               -> throwEdh ets EvalError "bogus scope object"
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
    _ -> exitEdh ets exit $ EdhString "bogus scope object"
    where !this = edh'scope'this $ contextScope $ edh'context ets


  -- this is called in case a ProgramHalt is constructed by Edh code
  haltAllocator _ !apk !exit = case apk of
    ArgsPack [] !kwargs | odNull kwargs -> createErr nil
    ArgsPack [v] !kwargs | odNull kwargs -> createErr v
    _ -> createErr $ EdhArgsPack apk
   where
    createErr !hv = exit =<< HostStore <$> newTVar
      (toDyn $ toException $ ProgramHalt $ toDyn hv)

  -- creating an IOError from Edh code
  ioErrAllocator !ets apk@(ArgsPack !args !kwargs) !exit = case args of
    [EdhString !m] | odNull kwargs -> createErr $ T.unpack m
    _                              -> edhValueRepr ets (EdhArgsPack apk)
      $ \ !repr -> createErr $ T.unpack repr
   where
    createErr !msg = exit =<< HostStore <$> newTVar
      (toDyn $ toException $ EdhIOError $ toException $ userError msg)

  -- a peer error is most prolly created from Edh code
  peerErrAllocator _ !apk !exit = exit =<< HostStore <$> newTVar
    (toDyn $ toException peerError)
   where
    peerError = case apk of
      (ArgsPack [EdhString !peerSite, EdhString !details] !kwargs)
        | odNull kwargs -> EdhPeerError peerSite details
      _ -> EdhPeerError "<bogus-peer>" $ T.pack $ show apk

  -- creating a tagged Edh error from Edh code
  errAllocator !tag !ets apk@(ArgsPack !args !kwargs) !exit = case args of
    [EdhString !m] | odNull kwargs' -> createErr m nil
    (EdhString !m : args') -> createErr m (EdhArgsPack $ ArgsPack args' kwargs)
    _ -> createErr "❌" (EdhArgsPack apk)
   where
    createErr !msg !details = exit =<< HostStore <$> newTVar
      (toDyn $ toException $ EdhError tag msg (toDyn details) cc)
    (!maybeUnwind, !kwargs') = odTakeOut (AttrByName "unwind") kwargs
    !unwind                  = case maybeUnwind of
      Just (EdhDecimal d) -> case decimalToInteger d of
        Just !n -> fromIntegral n
        _       -> 1
      _ -> 1
    !cc = getEdhCallContext unwind ets

  mthErrRepr :: EdhHostProc
  mthErrRepr _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> readTVar hsv >>= \ !hsd -> case fromDynamic hsd of
      Just (exc :: SomeException) -> case edhKnownError exc of
        Just (ProgramHalt !dhv) -> case fromDynamic dhv of
          Just (val :: EdhValue) -> edhValueRepr ets val $ \ !repr ->
            exitEdh ets exit $ EdhString $ errClsName <> "(" <> repr <> ")"
          Nothing -> exitEdh ets exit $ EdhString $ errClsName <> "()"
        Just (EdhIOError !exc') ->
          exitEdh ets exit
            $  EdhString
            $  errClsName
            <> "("
            <> T.pack (show $ show exc')
            <> ")"
        Just (EdhPeerError !peerSite !details) ->
          exitEdh ets exit
            $  EdhString
            $  errClsName
            <> "("
            <> T.pack (show peerSite)
            <> ","
            <> T.pack (show details)
            <> ")"
        Just (EdhError _tag !msg _details _cc) -> if T.null msg
          then exitEdh ets exit $ EdhString $ errClsName <> "()"
          else exitEdh ets exit $ EdhString $ errClsName <> "(`" <> msg <> "`)"
        _ -> exitEdh ets exit $ EdhString $ errClsName <> "()"
      Nothing -> exitEdh ets exit $ EdhString $ errClsName <> "()"
    _ -> exitEdh ets exit $ EdhString $ errClsName <> "()"
   where
    !errObj     = edh'scope'this $ contextScope $ edh'context ets
    !errClsName = objClassName errObj

  mthErrShow :: EdhHostProc
  mthErrShow _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> readTVar hsv >>= \ !hsd -> case fromDynamic hsd of
      Just (exc :: SomeException) -> case edhKnownError exc of
        Just err@(EdhError _errTag _errMsg !details _cc) -> do
          let !detailsText = case fromDynamic details of
                Just EdhNil -> ""
                Just _      -> "\n * with more detailed data."
                _           -> ""
          exitEdh ets exit $ EdhString $ T.pack (show err) <> detailsText
        _ -> exitEdh ets exit $ EdhString $ errClsName <> ": " <> T.pack
          (show exc)
      _ ->
        exitEdh ets exit $ EdhString $ "bogus error object of: " <> errClsName
    _ -> exitEdh ets exit $ EdhString $ "bogus error object of: " <> errClsName
   where
    !errObj     = edh'scope'this $ contextScope $ edh'context ets
    !errClsName = objClassName errObj

  mthErrDesc :: EdhHostProc
  mthErrDesc _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> readTVar hsv >>= \ !hsd -> case fromDynamic hsd of
      Just (exc :: SomeException) -> case edhKnownError exc of
        Just err@(EdhError _errTag _errMsg !details _cc) ->
          case fromDynamic details of
            Just EdhNil      -> exitEdh ets exit $ EdhString $ T.pack (show err)
            Just !detailsVal -> edhValueStr ets detailsVal $ \ !detailsStr ->
              exitEdh ets exit
                $  EdhString
                $  T.pack (show err)
                <> "\n * details:\n"
                <> detailsStr
            _ -> exitEdh ets exit $ EdhString $ T.pack (show err)
        _ ->
          exitEdh ets exit $ EdhString $ errClsName <> ": " <> T.pack (show exc)
      _ ->
        exitEdh ets exit $ EdhString $ "bogus error object of: " <> errClsName
    _ -> exitEdh ets exit $ EdhString $ "bogus error object of: " <> errClsName
   where
    !errObj     = edh'scope'this $ contextScope $ edh'context ets
    !errClsName = objClassName errObj

  mthErrStackGetter :: EdhHostProc
  mthErrStackGetter _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
      Just (exc :: SomeException) -> case edhKnownError exc of
        Just (EdhError _errTag _errMsg _details (EdhCallContext !tip !frames))
          -> exitEdh ets exit $ EdhArgsPack $ ArgsPack
            (EdhString . dispEdhCallFrame <$> frames)
            (odFromList [(AttrByName "tip", EdhString tip)])
        _ -> exitEdh ets exit nil
      _ -> exitEdh ets exit nil
    _ -> exitEdh ets exit nil
    where !errObj = edh'scope'this $ contextScope $ edh'context ets

  mthErrMsgGetter :: EdhHostProc
  mthErrMsgGetter _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
      Just (exc :: SomeException) -> case edhKnownError exc of
        Just (EdhError _errTag !errMsg _errDetails _errCtx) ->
          exitEdh ets exit $ EdhString errMsg
        _ -> exitEdh ets exit nil
      _ -> exitEdh ets exit nil
    _ -> exitEdh ets exit nil
    where !errObj = edh'scope'this $ contextScope $ edh'context ets

  mthErrDetailsGetter :: EdhHostProc
  mthErrDetailsGetter _ !exit !ets = case edh'obj'store errObj of
    HostStore !hsv -> fromDynamic <$> readTVar hsv >>= \case
      Just (exc :: SomeException) -> case edhKnownError exc of
        Just (EdhError _errTag _errMsg !errDetails _errCtx) ->
          case fromDynamic errDetails of
            Just (detailsValue :: EdhValue) -> exitEdh ets exit detailsValue
            _                               -> exitEdh ets exit nil
        _ -> exitEdh ets exit nil
      _ -> exitEdh ets exit nil
    _ -> exitEdh ets exit nil
    where !errObj = edh'scope'this $ contextScope $ edh'context ets


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
      exitEdh ets exit $ EdhString $ "<module: " <> pathStr <> ">"
    where !this = edh'scope'this $ contextScope $ edh'context ets

  mthModuClsShow :: EdhHostProc
  mthModuClsShow _ !exit !ets = do
    !path <- lookupEdhSelfAttr this (AttrByName "__path__")
    !file <- lookupEdhSelfAttr this (AttrByName "__file__")
    edhValueStr ets path $ \ !pathStr -> edhValueStr ets file $ \ !fileStr ->
      exitEdh ets exit
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
            (toDyn nil)
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

