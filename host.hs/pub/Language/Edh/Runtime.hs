
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

import           Language.Edh.Control
import           Language.Edh.Args
import           Language.Edh.InterOp
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.PkgMan
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.Evaluate


createEdhWorld :: MonadIO m => EdhConsole -> m EdhWorld
createEdhWorld !console = liftIO $ do

  -- the meta class
  !idMeta  <- newUnique
  !hsMeta  <- atomically iopdEmpty
  !ssMeta  <- newTVarIO []
  !mroMeta <- newTVarIO [] -- no super class, and self is not stored

  -- the root object and root scope
  !idRoot  <- newUnique
  !hsRoot  <- atomically
    $ iopdFromList [(AttrByName "__name__", EdhString "<root>")]
  !ssRoot    <- newTVarIO []

  -- the sandbox object and sandbox scope
  !idSandbox <- newUnique
  !hsSandbox <- atomically
    $ iopdFromList [(AttrByName "__name__", EdhString "<sandbox>")]
  !ssSandbox    <- newTVarIO []
  !mroSandbox   <- newTVarIO [] -- no super class, and self is not stored

  -- the namespace class, root object is a special instance of namespace class
  !idNamespace  <- newUnique
  !hsNamespace  <- atomically iopdEmpty
  !ssNamespace  <- newTVarIO []
  !mroNamespace <- newTVarIO [] -- no super class, and self is not stored

  let
    rootScope =
      Scope hsRoot rootObj rootObj defaultEdhExcptHndlr rootProc genesisStmt []
    rootProc = ProcDefi idRoot
                        (AttrByName "<root>")
                        rootScope
                        (Just ["the root namespace"])
                        (HostDecl phantomHostProc)
    rootObj      = Object idRoot (HashStore hsRoot) nsClassObj ssRoot

    sandboxScope = Scope hsSandbox
                         sandboxObj
                         sandboxObj
                         defaultEdhExcptHndlr
                         sandboxProc
                         genesisStmt
                         []
    sandboxProc = ProcDefi idSandbox
                           (AttrByName "<sandbox>")
                           sandboxScope
                           (Just ["the sandbox namespace"])
                           (HostDecl phantomHostProc)
    sandboxObj =
      Object idSandbox (HashStore hsSandbox) sandboxClassObj ssSandbox
    sandboxClass = Class sandboxProc hsSandbox phantomAllocator mroSandbox
    sandboxClassObj =
      Object idSandbox (ClassStore sandboxClass) metaClassObj ssSandbox

    metaProc = ProcDefi idMeta
                        (AttrByName "class")
                        rootScope
                        (Just ["the meta class"])
                        (HostDecl phantomHostProc)
    metaClass    = Class metaProc hsMeta phantomAllocator mroMeta
    metaClassObj = Object idMeta (ClassStore metaClass) metaClassObj ssMeta

    nsProc       = ProcDefi idNamespace
                            (AttrByName "<namespace>")
                            rootScope
                            (Just ["the namespace class"])
                            (HostDecl phantomHostProc)
    nsClass = Class nsProc hsNamespace phantomAllocator mroNamespace
    nsClassObj =
      Object idNamespace (ClassStore nsClass) metaClassObj ssNamespace

  atomically
    $  (flip iopdUpdate hsMeta =<<)
    $  sequence
    -- todo more static attrs for class objects here
    $  [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm hp
       | (nm, hp) <-
         [ ("__repr__", wrapHostProc mthClassRepr)
         , ("__show__", wrapHostProc mthClassShow)
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty rootScope nm getter setter
       | (nm, getter, setter) <-
         [ ("name", mthClassNameGetter, Nothing)
         , ("mro" , mthClassMROGetter , Nothing)
         ]
       ]

  atomically
    $ (flip iopdUpdate hsNamespace =<<)
    $ sequence
    $ [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm hp
      | (nm, hp) <-
        [ ("__repr__", wrapHostProc mthNsRepr)
        , ("__show__", wrapHostProc mthNsShow)
        , ("__desc__", wrapHostProc mthNsDesc)
        ]
      ]
  atomically
    $ iopdUpdate [(AttrByName "namespace", EdhObject nsClassObj)] hsRoot

  -- * the `scope` class
  !hsScope <-
    atomically
    $  (iopdFromList =<<)
    $  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm hp
       | (nm, hp) <-
         [ ("__repr__", wrapHostProc mthScopeRepr)
         , ("__show__", wrapHostProc mthScopeShow)
         , ("eval"    , wrapHostProc mthScopeEval)
         , ("get"     , wrapHostProc mthScopeGet)
         , ("put"     , wrapHostProc mthScopePut)
         , ("attrs"   , wrapHostProc mthScopeAttrs)
         ]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty rootScope nm getter setter
       | (nm, getter, setter) <-
         [ ("outer"    , mthScopeOuterGetter, Nothing)
         , ("lexiLoc"  , mthScopeLexiLoc    , Nothing)
         , ("callerLoc", mthScopeCallerLoc  , Nothing)
         ]
       ]
  let scopeAllocator :: "ofObj" ?: Object -> EdhObjectAllocator
      scopeAllocator (optionalArg -> !maybeOfObj) !exit !ets =
        case maybeOfObj of
          Just !obj ->
            objectScope obj >>= \ !objScope -> exit $ HostStore $ toDyn objScope
          Nothing -> exit $ HostStore $ toDyn $ contextScope $ edh'context ets
  !clsScope <- atomically
    $ mkHostClass' rootScope "scope" (allocEdhObj scopeAllocator) hsScope []
  let edhWrapScope :: Scope -> STM Object
      edhWrapScope !scope = do
        !idScope <- unsafeIOToSTM newUnique
        !ss      <- newTVar []
        return Object { edh'obj'ident  = idScope
                      , edh'obj'store  = HostStore $ toDyn scope
                      , edh'obj'class  = clsScope
                      , edh'obj'supers = ss
                      }
  atomically $ iopdUpdate [(AttrByName "scope", EdhObject clsScope)] hsRoot

  -- * error classes
  !hsErrCls <-
    atomically
    $  (iopdFromList =<<)
    $  sequence
    $  [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm hp
       | (nm, hp) <-
         [ ("__repr__", wrapHostProc mthErrRepr)
         , ("__show__", wrapHostProc mthErrShow)
         , ("__desc__", wrapHostProc mthErrDesc)
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
    $ mkHostClass' rootScope "ProgramHalt" haltAllocator hsErrCls []
  clsIOError <- atomically
    $ mkHostClass' rootScope "IOError" ioErrAllocator hsErrCls []
  clsPeerError <- atomically
    $ mkHostClass' rootScope "PeerError" peerErrAllocator hsErrCls []
  clsException <- atomically
    $ mkHostClass' rootScope "Exception" (errAllocator EdhException) hsErrCls []
  clsPackageError <- atomically $ mkHostClass' rootScope
                                               "PackageError"
                                               (errAllocator PackageError)
                                               hsErrCls
                                               []
  clsParseError <- atomically $ mkHostClass' rootScope
                                             "ParseError"
                                             (errAllocator ParseError)
                                             hsErrCls
                                             []
  clsEvalError <- atomically
    $ mkHostClass' rootScope "EvalError" (errAllocator EvalError) hsErrCls []
  clsUsageError <- atomically
    $ mkHostClass' rootScope "UsageError" (errAllocator UsageError) hsErrCls []

  let edhWrapException :: SomeException -> STM Object
      edhWrapException !exc = do
        !uidErr    <- unsafeIOToSTM newUnique
        !supersErr <- newTVar []
        case edhKnownError exc of
          Just !err -> do
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
            return $ Object uidErr
                            (HostStore $ toDyn $ toException err)
                            clsErr
                            supersErr
          Nothing -> return $ Object
            uidErr
            (HostStore $ toDyn $ toException $ EdhIOError exc)
            clsIOError
            supersErr

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
    $ [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm hp
      | (nm, hp) <-
        [ ("__repr__", wrapHostProc mthModuClsRepr)
        , ("__show__", wrapHostProc mthModuClsShow)
        ]
      ]
  !clsModule <- atomically
    $ mkHostClass' rootScope "module" (allocEdhObj moduleAllocator) hsModuCls []
  atomically $ iopdUpdate [(AttrByName "module", EdhObject clsModule)] hsRoot


  -- * operator precedence dict
  opPD  <- newTMVarIO Map.empty

  -- * the container of loaded modules
  modus <- newTMVarIO Map.empty

  -- assembly the world with pieces prepared above
  let world = EdhWorld { edh'world'root        = rootScope
                       , edh'world'sandbox     = sandboxScope
                       , edh'world'operators   = opPD
                       , edh'world'modules     = modus
                       , edh'world'console     = console
                       , edh'scope'wrapper     = edhWrapScope
                       , edh'exception'wrapper = edhWrapException
                       , edh'module'class      = clsModule
                       }

  return world
 where

  phantomAllocator :: ArgsPack -> EdhObjectAllocator
  phantomAllocator _ _ !ets =
    throwEdh ets EvalError "bug: allocating phantom object"
  phantomHostProc :: ArgsPack -> EdhHostProc
  phantomHostProc _apk _exit =
    throwEdhTx EvalError "bug: calling phantom procedure"

  genesisStmt :: StmtSrc
  genesisStmt = StmtSrc (startPosOfFile "<genesis>", VoidStmt)


  mthClassRepr :: EdhHostProc
  mthClassRepr !exit !ets = case edh'obj'store clsObj of
    ClassStore !cls ->
      exitEdh ets exit $ EdhString $ procedureName (edh'class'proc cls)
    _ -> exitEdh ets exit $ EdhString "<bogus-class>"
    where !clsObj = edh'scope'that $ contextScope $ edh'context ets

  mthClassShow :: EdhHostProc
  mthClassShow !exit !ets = case edh'obj'store clsObj of
    ClassStore !cls ->
      exitEdh ets exit $ EdhString $ "class: " <> procedureName
        (edh'class'proc cls)
    _ -> exitEdh ets exit $ EdhString "<bogus-class>"
    where !clsObj = edh'scope'that $ contextScope $ edh'context ets

  mthClassNameGetter :: EdhHostProc
  mthClassNameGetter !exit !ets = case edh'obj'store clsObj of
    ClassStore !cls ->
      exitEdh ets exit $ attrKeyValue $ edh'procedure'name (edh'class'proc cls)
    _ -> exitEdh ets exit nil
    where !clsObj = edh'scope'that $ contextScope $ edh'context ets

  mthClassMROGetter :: EdhHostProc
  mthClassMROGetter !exit !ets = case edh'obj'store clsObj of
    ClassStore !cls -> do
      !mro <- readTVar $ edh'class'mro cls
      exitEdh ets exit $ EdhArgsPack $ ArgsPack (EdhObject <$> mro) odEmpty
    _ -> exitEdh ets exit nil
    where !clsObj = edh'scope'that $ contextScope $ edh'context ets



  mthNsRepr :: EdhHostProc
  mthNsRepr !exit !ets = exitEdh ets exit . EdhString =<< nsRepr
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
  mthNsShow !exit !ets = exitEdh ets exit . EdhString =<< nsShow
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
  mthNsDesc !exit !ets = exitEdh ets exit . EdhString =<< nsDesc
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
  mthScopeRepr !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus scope object>")
      $ \(scope :: Scope) ->
          exitEdh ets exit
            $  EdhString
            $  "<scope: "
            <> procedureName (edh'scope'proc scope)
            <> ">"

  mthScopeShow :: EdhHostProc
  mthScopeShow !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "bogus scope object")
      $ \(scope :: Scope) -> scopeLexiLoc scope $ \ !lexiLoc -> do
          let StmtSrc (!callerSrcLoc, _) = edh'scope'caller scope
          exitEdh ets exit
            $  EdhString
            $  "#scope@ "
            <> lexiLoc
            <> "\n#called by: "
            <> T.pack (prettySourceLoc callerSrcLoc)

  mthScopeCallerLoc :: EdhHostProc
  mthScopeCallerLoc !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus scope object>")
      $ \(scope :: Scope) -> do
          let StmtSrc (!callerSrcLoc, _) = edh'scope'caller scope
          exitEdh ets exit $ EdhString $ T.pack (prettySourceLoc callerSrcLoc)

  mthScopeLexiLoc :: EdhHostProc
  mthScopeLexiLoc !exit !ets =
    withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus scope object>")
      $ \(scope :: Scope) -> scopeLexiLoc scope
          $ \ !lexiLoc -> exitEdh ets exit $ EdhString lexiLoc

  mthScopeAttrs :: EdhHostProc
  mthScopeAttrs !exit !ets =
    withThisHostObj' ets (throwEdh ets EvalError "bogus scope object")
      $ \(scope :: Scope) ->
          (iopdSnapshot (edh'scope'entity scope) >>=)
            $ exitEdh ets exit
            . EdhArgsPack
            . ArgsPack []

  mthScopeGet :: ArgsPack -> EdhHostProc
  mthScopeGet (ArgsPack !args !kwargs) !exit !ets =
    withThisHostObj' ets (throwEdh ets EvalError "bogus scope object")
      $ \(scope :: Scope) -> do
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
                  lookupAttrs (attrVal : rtnArgs)
                              rtnKwArgs
                              restArgs
                              kwargs'
                              exit'
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

  mthScopePut :: ArgsPack -> EdhHostProc
  mthScopePut (ArgsPack !args !kwargs) !exit !ets =
    withThisHostObj' ets (throwEdh ets EvalError "bogus scope object")
      $ \(scope :: Scope) -> do
          let !es = edh'scope'entity scope
              putAttrs
                :: [EdhValue]
                -> [(AttrKey, EdhValue)]
                -> ([(AttrKey, EdhValue)] -> STM ())
                -> STM ()
              putAttrs []         cumu !exit' = exit' cumu
              putAttrs (a : rest) cumu !exit' = case a of
                EdhPair (EdhString !k) !v ->
                  putAttrs rest ((AttrByName k, v) : cumu) exit'
                EdhPair (EdhSymbol !k) !v ->
                  putAttrs rest ((AttrBySym k, v) : cumu) exit'
                _ -> edhValueDesc ets a $ \ !badDesc ->
                  throwEdh ets UsageError
                    $  "invalid key/value pair to put into a scope - "
                    <> badDesc
          putAttrs args [] $ \ !attrs -> do
            iopdUpdate (attrs ++ odToList kwargs) es
            exitEdh ets exit nil

  mthScopeEval :: ArgsPack -> EdhHostProc
  mthScopeEval (ArgsPack !args !kwargs) !exit !ets =
    withThisHostObj' ets (throwEdh ets EvalError "bogus scope object")
      $ \(scope :: Scope) -> do
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
                  _ ->
                    EdhArgsPack $ ArgsPack (reverse argsValues) $ odFromList
                      kwargsValues
            evalThePack !argsValues [] (kwExpr : kwargsExprs') = case kwExpr of
              (!kw, EdhExpr _ !expr _) ->
                runEdhTx etsEval $ evalExpr expr $ \ !val _ets -> do
                  edhSetValue kw (edhDeCaseWrap val) kwIOPD
                  evalThePack argsValues [] kwargsExprs'
              !v -> throwEdh ets EvalError $ "not an expr: " <> T.pack (show v)
            evalThePack !argsValues (argExpr : argsExprs') !kwargsExprs =
              case argExpr of
                EdhExpr _ !expr _ ->
                  runEdhTx etsEval $ evalExpr expr $ \ !val _ets -> evalThePack
                    (edhDeCaseWrap val : argsValues)
                    argsExprs'
                    kwargsExprs
                !v ->
                  throwEdh ets EvalError $ "not an expr: " <> T.pack (show v)
          evalThePack [] args $ odToList kwargs

  mthScopeOuterGetter :: EdhHostProc
  mthScopeOuterGetter !exit !ets = case edh'obj'store this of
    HostStore !hsd -> case fromDynamic hsd of
      Nothing               -> throwEdh ets EvalError "bogus scope object"
      Just (scope :: Scope) -> case outerScopeOf scope of
        Nothing -> exitEdh ets exit nil
        Just !outerScope ->
          edhMutCloneObj ets
                         this
                         (edh'scope'that procScope)
                         (HostStore $ toDyn outerScope)
            $ \ !outerScopeObj -> exitEdh ets exit $ EdhObject outerScopeObj
    _ -> exitEdh ets exit $ EdhString "bogus scope object"
   where
    !procScope = contextScope $ edh'context ets
    !this      = edh'scope'this procScope


  -- this is called in case a ProgramHalt is constructed by Edh code
  haltAllocator !apk !exit _ = case apk of
    ArgsPack [] !kwargs | odNull kwargs -> createErr nil
    ArgsPack [v] !kwargs | odNull kwargs -> createErr v
    _ -> createErr $ EdhArgsPack apk
   where
    createErr !hv =
      exit $ HostStore $ toDyn $ toException $ ProgramHalt $ toDyn hv

  -- creating an IOError from Edh code
  ioErrAllocator apk@(ArgsPack !args !kwargs) !exit !ets = case args of
    [EdhString !m] | odNull kwargs -> createErr $ T.unpack m
    _                              -> edhValueRepr ets (EdhArgsPack apk)
      $ \ !repr -> createErr $ T.unpack repr
   where
    createErr !msg =
      exit
        $ HostStore
        $ toDyn
        $ toException
        $ EdhIOError
        $ toException
        $ userError msg

  -- a peer error is most prolly created from Edh code
  peerErrAllocator !apk !exit _ = exit $ HostStore $ toDyn $ toException
    peerError
   where
    peerError = case apk of
      (ArgsPack [EdhString !peerSite, EdhString !details] !kwargs)
        | odNull kwargs -> EdhPeerError peerSite details
      _ -> EdhPeerError "<bogus-peer>" $ T.pack $ show apk

  -- creating a tagged Edh error from Edh code
  errAllocator !tag !apk !exit !ets =
    exit $ HostStore $ toDyn $ toException $ edhCreateError 0 ets tag apk

  mthErrRepr :: EdhHostProc
  mthErrRepr !exit !ets = case edh'obj'store errObj of
    HostStore !hsd -> case fromDynamic hsd of
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
    !scope      = contextScope $ edh'context ets
    !errObj     = edh'scope'this scope
    !endErr     = edh'scope'that scope
    !errClsName = objClassName endErr

  mthErrShow :: EdhHostProc
  mthErrShow !exit !ets = case edh'obj'store errObj of
    HostStore !hsd -> case fromDynamic hsd of
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
  mthErrDesc !exit !ets = case edh'obj'store errObj of
    HostStore !hsd -> case fromDynamic hsd of
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
  mthErrStackGetter !exit !ets = case edh'obj'store errObj of
    HostStore !hsd -> case fromDynamic hsd of
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
  mthErrMsgGetter !exit !ets = case edh'obj'store errObj of
    HostStore !hsd -> case fromDynamic hsd of
      Just (exc :: SomeException) -> case edhKnownError exc of
        Just (EdhError _errTag !errMsg _errDetails _errCtx) ->
          exitEdh ets exit $ EdhString errMsg
        _ -> exitEdh ets exit nil
      _ -> exitEdh ets exit nil
    _ -> exitEdh ets exit nil
    where !errObj = edh'scope'this $ contextScope $ edh'context ets

  mthErrDetailsGetter :: EdhHostProc
  mthErrDetailsGetter !exit !ets = case edh'obj'store errObj of
    HostStore !hsd -> case fromDynamic hsd of
      Just (exc :: SomeException) -> case edhKnownError exc of
        Just (EdhError _errTag _errMsg !errDetails _errCtx) ->
          case fromDynamic errDetails of
            Just (detailsValue :: EdhValue) -> exitEdh ets exit detailsValue
            _                               -> exitEdh ets exit nil
        _ -> exitEdh ets exit nil
      _ -> exitEdh ets exit nil
    _ -> exitEdh ets exit nil
    where !errObj = edh'scope'this $ contextScope $ edh'context ets


  moduleAllocator
    :: "__name__" !: Text
    -> "__path__" ?: Text
    -> "__file__" ?: Text
    -> RestKwArgs
    -> EdhObjectAllocator
  moduleAllocator (mandatoryArg -> !moduName) (defaultArg "<ad-hoc>" -> !moduPath) (defaultArg "<on-the-fly>" -> !moduFile) !extraArts !exit _ets
    = exit =<< HashStore <$> iopdFromList moduArts
   where
    moduArts =
      odToList extraArts
        ++ [ (AttrByName "__name__", EdhString moduName)
           , (AttrByName "__path__", EdhString moduPath)
           , (AttrByName "__file__", EdhString moduFile)
           ]

  mthModuClsRepr :: EdhHostProc
  mthModuClsRepr !exit !ets = do
    !path <- lookupEdhSelfAttr this (AttrByName "__path__")
    edhValueStr ets path $ \ !pathStr ->
      exitEdh ets exit $ EdhString $ "<module: " <> pathStr <> ">"
    where !this = edh'scope'this $ contextScope $ edh'context ets

  mthModuClsShow :: EdhHostProc
  mthModuClsShow !exit !ets = do
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


declareEdhOperators
  :: EdhWorld -> OpDeclLoc -> [(OpSymbol, OpFixity, Precedence)] -> STM ()
declareEdhOperators world declLoc opps = do
  opPD  <- takeTMVar wops
  opPD' <-
    sequence
    $ Map.unionWithKey chkCompatible (return <$> opPD)
    $ Map.fromList
    $ (<$> opps)
    $ \(sym, fixity, precedence) -> (sym, return (fixity, precedence, declLoc))
  putTMVar wops opPD'
 where
  !wops = edh'world'operators world
  chkCompatible
    :: OpSymbol
    -> STM (OpFixity, Precedence, Text)
    -> STM (OpFixity, Precedence, Text)
    -> STM (OpFixity, Precedence, Text)
  chkCompatible sym prev newly = do
    (prevFixity, prevPrec, prevDeclLoc) <- prev
    (newFixity , newPrec , newDeclLoc ) <- newly
    if prevPrec /= newPrec
      then
        throwSTM
        $ EdhError
            UsageError
            (  "precedence change from "
            <> T.pack (show prevPrec)
            <> " (declared at "
            <> prevDeclLoc
            <> ") to "
            <> T.pack (show newPrec)
            <> " (declared at "
            <> T.pack (show newDeclLoc)
            <> ") for operator: "
            <> sym
            )
            (toDyn nil)
        $ EdhCallContext "<edh>" []
      else case newFixity of
        Infix -> return (prevFixity, prevPrec, prevDeclLoc)
        _     -> if newFixity /= prevFixity
          then
            throwSTM
            $ EdhError
                UsageError
                (  "fixity change from "
                <> T.pack (show prevFixity)
                <> " (declared at "
                <> prevDeclLoc
                <> ") to "
                <> T.pack (show newFixity)
                <> " (declared at "
                <> T.pack (show newDeclLoc)
                <> ") for operator: "
                <> sym
                )
                (toDyn nil)
            $ EdhCallContext "<edh>" []
          else return (newFixity, prevPrec, prevDeclLoc)


haltEdhProgram :: EdhThreadState -> EdhValue -> STM ()
haltEdhProgram !ets !hv =
  edhWrapException (toException $ ProgramHalt $ toDyn hv)
    >>= \ !exo -> edhThrow ets $ EdhObject exo
 where
  !edhWrapException =
    edh'exception'wrapper (edh'prog'world $ edh'thread'prog ets)


runEdhProgram :: MonadIO m => EdhWorld -> EdhTx -> m (Either EdhError EdhValue)
runEdhProgram !world !prog =
  liftIO $ tryJust edhKnownError $ runEdhProgram' world prog

runEdhProgram' :: MonadIO m => EdhWorld -> EdhTx -> m EdhValue
runEdhProgram' !world !prog = liftIO $ do
  !haltResult <- atomically newEmptyTMVar
  driveEdhProgram haltResult world prog
  liftIO (atomically $ tryReadTMVar haltResult) >>= \case
    Nothing        -> return nil
    Just (Right v) -> return v
    Just (Left  e) -> throwIO e


createEdhModule
  :: MonadIO m => EdhWorld -> Text -> ModuleId -> String -> m Object
createEdhModule !world !moduName !moduId !srcName =
  liftIO $ atomically $ edhCreateModule world moduName moduId srcName


type EdhModulePreparation = EdhThreadState -> STM () -> STM ()
edhModuleAsIs :: EdhModulePreparation
edhModuleAsIs _ets !exit = exit


installEdhModule
  :: MonadIO m => EdhWorld -> ModuleId -> EdhModulePreparation -> m Object
installEdhModule !world !moduId !preInstall = liftIO $ do
  !modu <- createEdhModule world moduId moduId "<host-module>"
  void $ runEdhProgram' world $ \ !ets ->
    moduleContext world modu >>= \ !moduCtx ->
      preInstall ets { edh'context = moduCtx } $ do
        !moduSlot <- newTVar $ ModuLoaded modu
        !moduMap  <- takeTMVar (edh'world'modules world)
        putTMVar (edh'world'modules world) $ Map.insert moduId moduSlot moduMap
  return modu

installedEdhModule :: MonadIO m => EdhWorld -> ModuleId -> m (Maybe Object)
installedEdhModule !world !moduId =
  liftIO $ atomically $ tryReadTMVar (edh'world'modules world) >>= \case
    Nothing  -> return Nothing
    Just !mm -> case Map.lookup moduId mm of
      Nothing           -> return Nothing
      Just !moduSlotVar -> readTVar moduSlotVar >>= \case
        ModuLoaded !modu         -> return $ Just modu
        ModuLoading !loadScope _ -> return $ Just $ edh'scope'this loadScope
        _                        -> return Nothing


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
runEdhModule' !world !impPath !preRun =
  liftIO $ locateEdhMainModule impPath >>= \(!moduName, !nomPath, !moduFile) ->
    streamDecodeUtf8With lenientDecode <$> B.readFile moduFile >>= \case
      Some !moduSource _ _ -> runEdhProgram' world $ \ !ets ->
        let !moduId = T.pack nomPath
        in  edhCreateModule world moduName moduId moduFile >>= \ !modu ->
              moduleContext world modu >>= \ !moduCtx ->
                let !etsModu = ets { edh'context = moduCtx }
                in  preRun etsModu $ runEdhTx etsModu $ evalEdh moduFile
                                                                moduSource
                                                                endOfEdh


runEdhFile :: MonadIO m => EdhWorld -> FilePath -> m (Either EdhError EdhValue)
runEdhFile !world !edhFile =
  liftIO $ tryJust edhKnownError $ runEdhFile' world edhFile

runEdhFile' :: MonadIO m => EdhWorld -> FilePath -> m EdhValue
runEdhFile' !world !edhFile =
  liftIO $ streamDecodeUtf8With lenientDecode <$> B.readFile edhFile >>= \case
    Some !moduSource _ _ -> runEdhProgram' world $ \ !ets ->
      edhCreateModule world "__main__" "__main__" edhFile >>= \ !modu ->
        moduleContext world modu >>= \ !moduCtx ->
          let !etsModu = ets { edh'context = moduCtx }
          in  runEdhTx etsModu $ evalEdh edhFile moduSource endOfEdh


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

