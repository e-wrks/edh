{-# LANGUAGE ImplicitParams #-}

module Language.Edh.Runtime where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import qualified Data.ByteString as B
import Data.Dynamic
import qualified Data.HashMap.Strict as Map
import Data.IORef
import qualified Data.List as L
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding
import Data.Text.Encoding.Error
import Language.Edh.Args
import Language.Edh.Batteries.InterOp
import Language.Edh.Control
import Language.Edh.CoreLang
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.PkgMan
import Language.Edh.RUID
import Language.Edh.RtTypes
import Language.Edh.Utils
import System.Directory
import System.Environment
import System.FilePath
import System.Posix.Signals
import Prelude

createEdhWorld :: EdhConsole -> IO EdhWorld
createEdhWorld !console = do
  -- the meta class
  !idMeta <- newRUID
  !hsMeta <- atomically iopdEmpty
  !ssMeta <- newTVarIO []
  !mroMeta <- newTVarIO [] -- no super class, and self is not stored

  -- the root object and root scope
  !idRoot <- newRUID
  !hsRoot <- atomically iopdEmpty
  !ssRoot <- newTVarIO []

  -- the sandbox object and sandbox scope
  !idSandbox <- newRUID
  !hsSandbox <- atomically iopdEmpty
  !ssSandbox <- newTVarIO []
  !mroSandbox <- newTVarIO [] -- no super class, and self is not stored

  -- the namespace class, root object is a special instance of namespace class
  !idNamespace <- newRUID
  !hsNamespace <- atomically iopdEmpty
  !ssNamespace <- newTVarIO []
  !mroNamespace <- newTVarIO [] -- no super class, and self is not stored
  let rootScope = Scope hsRoot rootObj rootObj rootProc []
      rootProc =
        ProcDefi
          idRoot
          (AttrByName "<root>")
          rootScope
          (DocCmt ["the root namespace"])
          (specialProc "<root>" "<world-root>")
      rootObj = Object (HashStore hsRoot) nsClassObj ssRoot

      sandboxScope = Scope hsSandbox sandboxObj sandboxObj sandboxProc []
      sandboxProc =
        ProcDefi
          idSandbox
          (AttrByName "<sandbox>")
          sandboxScope
          (DocCmt ["the sandbox namespace"])
          (specialProc "<sandbox>" "<world-root>")
      sandboxObj =
        Object (HashStore hsSandbox) sandboxClassObj ssSandbox
      sandboxClass = Class sandboxProc hsSandbox phantomAllocator mroSandbox
      sandboxClassObj =
        Object (ClassStore sandboxClass) metaClassObj ssSandbox

      metaProc =
        ProcDefi
          idMeta
          (AttrByName "class")
          rootScope
          (DocCmt ["the meta class"])
          (specialProc "<meta-class>" "<world-root>")
      metaClass = Class metaProc hsMeta phantomAllocator mroMeta
      metaClassObj = Object (ClassStore metaClass) metaClassObj ssMeta

      nsProc =
        ProcDefi
          idNamespace
          (AttrByName "namespace")
          rootScope
          (DocCmt ["the namespace class"])
          (specialProc "<meta-namespace>" "<world-root>")
      nsClass = Class nsProc hsNamespace phantomAllocator mroNamespace
      nsClassObj =
        Object (ClassStore nsClass) metaClassObj ssNamespace

  atomically $
    (flip iopdUpdate hsMeta =<<) $
      sequence
      -- todo more static attrs for class objects here
      $
        [ (AttrByName nm,) <$> mkHostProc rootScope EdhMethod nm hp
          | (nm, hp) <-
              [ ("__repr__", wrapHostProc mthClassRepr),
                ("__show__", wrapHostProc mthClassShow),
                ("__desc__", wrapHostProc mthClassDesc)
              ]
        ]
          ++ [ (AttrByName nm,) <$> mkHostProperty rootScope nm getter setter
               | (nm, getter, setter) <-
                   [ ("name", mthClassNameGetter, Nothing),
                     ("mro", mthClassMROGetter, Nothing)
                   ]
             ]

  atomically $
    (flip iopdUpdate hsNamespace =<<) $
      sequence $
        [ (AttrByName nm,) <$> mkHostProc rootScope EdhMethod nm hp
          | (nm, hp) <-
              [ ("__repr__", wrapHostProc mthNsRepr),
                ("__show__", wrapHostProc mthNsShow),
                ("__desc__", wrapHostProc mthNsDesc)
              ]
        ]
  atomically $
    iopdUpdate [(AttrByName "namespace", EdhObject nsClassObj)] hsRoot

  -- the host value wrapper class
  !hsHostValue <-
    atomically $
      (iopdFromList =<<) $
        sequence $
          [ (AttrByName nm,) <$> mkHostProc rootScope EdhMethod nm hp
            | (nm, hp) <-
                [ ("__repr__", wrapHostProc mthValueRepr)
                ]
          ]
  let hostValueAllocator :: EdhObjectAllocator
      hostValueAllocator _exit !ets =
        throwEdh ets UsageError "you can not create a host value from script"
  !clsHostValue <-
    atomically $
      mkHostClass'
        rootScope
        "<host-value>"
        (allocEdhObj hostValueAllocator)
        hsHostValue
        []
  let edhWrapValue :: Maybe Text -> HostValue -> STM Object
      edhWrapValue !maybeRepr !dd = do
        !cls <- case maybeRepr of
          Nothing -> return clsHostValue
          Just !repr -> do
            !hsCustRepr <-
              iopdFromList [(AttrByName "__repr__", EdhString repr)]
            case edh'obj'store clsHostValue of
              ClassStore !hsCls ->
                return
                  clsHostValue
                    { edh'obj'store =
                        ClassStore $ hsCls {edh'class'arts = hsCustRepr}
                    }
              _ -> error "bug: class not bearing ClassStore"
        !ss <- newTVar []
        return
          Object
            { edh'obj'store = HostStore dd,
              edh'obj'class = cls,
              edh'obj'supers = ss
            }

  -- the `scope` class
  !hsScope <-
    atomically $
      (iopdFromList =<<) $
        sequence $
          [ (AttrByName nm,) <$> mkHostProc rootScope EdhMethod nm hp
            | (nm, hp) <-
                [ ("__repr__", wrapHostProc mthScopeRepr),
                  ("__show__", wrapHostProc mthScopeShow),
                  ("eval", wrapHostProc mthScopeEval),
                  ("get", wrapHostProc mthScopeGet),
                  ("put", wrapHostProc mthScopePut),
                  ("attrs", wrapHostProc mthScopeAttrs)
                ]
          ]
            ++ [ (AttrByName nm,) <$> mkHostProperty rootScope nm getter setter
                 | (nm, getter, setter) <-
                     [ ("outer", mthScopeOuterGetter, Nothing),
                       ("lexiLoc", mthScopeLexiLoc, Nothing)
                     ]
               ]
  let scopeAllocator :: "ofObj" ?: Object -> EdhObjectAllocator
      scopeAllocator (optionalArg -> !maybeOfObj) !exit !ets =
        case maybeOfObj of
          Just !obj -> do
            !objScope <- objectScope obj
            exit $ HostStore $ wrapHostValue objScope
          Nothing ->
            exit $ HostStore $ wrapHostValue $ contextScope $ edh'context ets
  !clsScope <-
    atomically $
      mkHostClass' rootScope "scope" (allocEdhObj scopeAllocator) hsScope []
  let edhWrapScope :: Scope -> STM Object
      edhWrapScope !scope = do
        !ss <- newTVar []
        return
          Object
            { edh'obj'store = HostStore $ wrapHostValue scope,
              edh'obj'class = clsScope,
              edh'obj'supers = ss
            }
  atomically $ iopdUpdate [(AttrByName "scope", EdhObject clsScope)] hsRoot

  -- error classes
  !hsErrCls <-
    atomically $
      (iopdFromList =<<) $
        sequence $
          [ (AttrByName nm,) <$> mkHostProc rootScope EdhMethod nm hp
            | (nm, hp) <-
                [ ("__repr__", wrapHostProc mthErrRepr),
                  ("__show__", wrapHostProc mthErrShow),
                  ("__desc__", wrapHostProc mthErrDesc)
                ]
          ]
            ++ [ (AttrByName nm,) <$> mkHostProperty rootScope nm getter setter
                 | (nm, getter, setter) <-
                     [ ("context", mthErrCtxGetter, Nothing),
                       ("message", mthErrMsgGetter, Nothing),
                       ("details", mthErrDetailsGetter, Nothing)
                     ]
               ]
  !clsProgramHalt <-
    atomically $
      mkHostClass' rootScope "ProgramHalt" haltAllocator hsErrCls []
  !clsThreadTerminate <-
    atomically $
      mkHostClass' rootScope "ThreadTerminate" thTermAllocator hsErrCls []
  !clsIOError <-
    atomically $
      mkHostClass' rootScope "IOError" ioErrAllocator hsErrCls []
  !clsPeerError <-
    atomically $
      mkHostClass' rootScope "PeerError" peerErrAllocator hsErrCls []
  !clsException <-
    atomically $
      mkHostClass' rootScope "Exception" (errAllocator EdhException) hsErrCls []
  !clsPackageError <-
    atomically $
      mkHostClass'
        rootScope
        "PackageError"
        (errAllocator PackageError)
        hsErrCls
        []
  !clsParseError <-
    atomically $
      mkHostClass'
        rootScope
        "ParseError"
        (errAllocator ParseError)
        hsErrCls
        []
  !clsEvalError <-
    atomically $
      mkHostClass' rootScope "EvalError" (errAllocator EvalError) hsErrCls []
  !clsUsageError <-
    atomically $
      mkHostClass' rootScope "UsageError" (errAllocator UsageError) hsErrCls []
  !clsUserCancel <-
    atomically $
      mkHostClass' rootScope "UserCancel" (errAllocator UserCancel) hsErrCls []

  let edhWrapException :: Maybe EdhThreadState -> SomeException -> STM Object
      edhWrapException !etsMaybe !exc = do
        let exitWith :: Object -> SomeException -> STM Object
            exitWith cls xe = do
              !hs <- HostStore <$> pinHostValue xe
              !supersErr <- newTVar []
              return $ Object hs cls supersErr
        case edhKnownError exc of
          Just !err -> do
            let !clsErr = case err of
                  ProgramHalt {} -> clsProgramHalt
                  ThreadTerminate -> clsThreadTerminate
                  EdhIOError {} -> clsIOError
                  EdhPeerError {} -> clsPeerError
                  EdhError !et _ _ _ -> case et of
                    EdhException -> clsException
                    PackageError -> clsPackageError
                    ParseError -> clsParseError
                    EvalError -> clsEvalError
                    UsageError -> clsUsageError
                    UserCancel -> clsUserCancel
            exitWith clsErr $ toException err
          Nothing -> case fromException exc of
            Just (EdhHostError tag msg details) -> do
              let !err = EdhError tag msg details $
                    case etsMaybe of
                      Just !ets -> getEdhErrCtx 0 ets
                      Nothing -> "<RTS>"
              exitWith clsUserCancel $ toException err
            Nothing -> case fromException exc of
              Just UserInterrupt -> do
                let !err = EdhError UserCancel "Ctrl^C pressed" (toDyn nil) $
                      case etsMaybe of
                        Just !ets -> getEdhErrCtx 0 ets
                        Nothing -> "<RTS>"
                exitWith clsUserCancel $ toException err
              _ ->
                exitWith clsIOError $ toException $ EdhIOError exc

  atomically $
    iopdUpdate
      [ (AttrByName $ edhClassName clsObj, EdhObject clsObj)
        | clsObj <-
            [ clsProgramHalt,
              clsThreadTerminate,
              clsIOError,
              clsPeerError,
              clsException,
              clsPackageError,
              clsParseError,
              clsEvalError,
              clsUsageError,
              clsUserCancel
            ]
      ]
      hsRoot

  -- the `module` class
  !hsModuCls <-
    atomically $
      (iopdFromList =<<) $
        sequence $
          [ (AttrByName nm,) <$> mkHostProc rootScope mc nm hp
            | (nm, mc, hp) <-
                [ ("__repr__", EdhMethod, wrapHostProc mthModuRepr),
                  ("__show__", EdhMethod, wrapHostProc mthModuShow),
                  ("__call__", EdhIntrpr, wrapHostProc mthModuCall)
                ]
          ]
  !clsModule <-
    atomically $
      mkHostClass' rootScope "module" (allocEdhObj moduleAllocator) hsModuCls []
  atomically $ iopdUpdate [(AttrByName "module", EdhObject clsModule)] hsRoot

  -- operator precedence dict
  !opPD <- newTVarIO $ GlobalOpDict Map.empty []

  -- the meta host module
  !metaModu <-
    newTVarIO $
      ModuLoaded $
        Object
          { edh'obj'store = HashStore hsRoot,
            edh'obj'class = clsModule,
            edh'obj'supers = ssRoot
          }

  -- the container of loaded modules
  !modus <- newTMVarIO $ Map.fromList [(HostModule "batteries/meta", metaModu)]
  -- the container of cached fragments
  !frags <- newTVarIO Map.empty

  !trapReq <- newIORef 0
  -- record a trap request on SIGQUIT
  lookupEnv "EDH_TRAP_SIGQUIT" >>= \case
    Just "" -> pure ()
    Just "0" -> pure ()
    Just "off" -> pure ()
    Just "NO" -> pure ()
    _ -> addSignalHandler keyboardTermination $ modifyIORef' trapReq (+ 1)

  !rootEffects <- newTVarIO Map.empty
  -- assembly the world with pieces prepared above
  let !world =
        EdhWorld
          { edh'world'root = rootScope,
            edh'world'sandbox = sandboxScope,
            edh'world'operators = opPD,
            edh'world'modules = modus,
            edh'world'fragments = frags,
            edh'world'console = console,
            edh'value'wrapper = edhWrapValue,
            edh'scope'wrapper = edhWrapScope,
            edh'root'effects = rootEffects,
            edh'exception'wrapper = edhWrapException,
            edh'module'class = clsModule,
            edh'trap'request = trapReq
          }

  return world
  where
    specialProc :: Text -> Text -> ProcDecl
    specialProc n l =
      ProcDecl
        (AttrAddrSrc (QuaintAttr n) noSrcRange)
        NullaryReceiver
        Nothing
        (StmtSrc VoidStmt noSrcRange)
        (SrcLoc (SrcDoc l) noSrcRange)

    mthClassRepr :: EdhHostProc
    mthClassRepr !exit !ets = case edh'obj'store clsObj of
      ClassStore !cls ->
        exitEdh ets exit $ EdhString $ procedureName (edh'class'proc cls)
      _ -> exitEdh ets exit $ EdhString "<bogus-class>"
      where
        !clsObj = edh'scope'that $ contextScope $ edh'context ets

    mthClassShow :: EdhHostProc
    mthClassShow !exit !ets = case edh'obj'store clsObj of
      ClassStore !cls ->
        exitEdh ets exit $
          EdhString $ "class: " <> procedureName (edh'class'proc cls)
      _ -> exitEdh ets exit $ EdhString "<bogus-class>"
      where
        !clsObj = edh'scope'that $ contextScope $ edh'context ets

    mthClassDesc :: EdhHostProc
    mthClassDesc !exit !ets = case edh'obj'store clsObj of
      ClassStore !cls ->
        exitEdh ets exit $
          EdhString $
            "class: " <> procedureName (edh'class'proc cls)
              -- TODO show super classes it extends
              -- TODO show member methods / properties / static attrs etc.
              <> docString (edh'procedure'doc $ edh'class'proc cls)
      _ -> exitEdh ets exit $ EdhString "<bogus-class>"
      where
        !clsObj = edh'scope'that $ contextScope $ edh'context ets

        docString :: OptDocCmt -> Text
        docString NoDocCmt = ""
        docString (DocCmt !docCmt) =
          (("\n * doc comments *\n" <>) . T.unlines) docCmt

    mthClassNameGetter :: EdhHostProc
    mthClassNameGetter !exit !ets = case edh'obj'store clsObj of
      ClassStore !cls ->
        exitEdh ets exit $ attrKeyValue $ edh'procedure'name (edh'class'proc cls)
      _ -> exitEdh ets exit nil
      where
        !clsObj = edh'scope'that $ contextScope $ edh'context ets

    mthClassMROGetter :: EdhHostProc
    mthClassMROGetter !exit !ets = case edh'obj'store clsObj of
      ClassStore !cls -> do
        !mro <- readTVar $ edh'class'mro cls
        exitEdh ets exit $ EdhArgsPack $ ArgsPack (EdhObject <$> mro) odEmpty
      _ -> exitEdh ets exit nil
      where
        !clsObj = edh'scope'that $ contextScope $ edh'context ets

    mthNsRepr :: EdhHostProc
    mthNsRepr !exit !ets = do
      let !nsName = objClassName this
      exitEdh ets exit $ EdhString $ "<namespace: " <> nsName <> ">"
      where
        !scope = contextScope $ edh'context ets
        !this = edh'scope'this scope

    mthNsShow :: EdhHostProc
    mthNsShow !exit !ets = do
      let !nsName = objClassName this
      exitEdh ets exit $
        EdhString $ "It's a namespace named `" <> nsName <> "`"
      where
        !scope = contextScope $ edh'context ets
        !this = edh'scope'this scope

    mthNsDesc :: EdhHostProc
    mthNsDesc !exit !ets = do
      let !nsName = objClassName this
      !nAttrs <- case edh'obj'store this of
        HashStore !hs -> iopdSize hs
        _ -> return 0
      exitEdh ets exit $
        EdhString $
          "It's a namespace named `" <> nsName <> "`, with "
            <> T.pack (show nAttrs)
            <> " attribute(s)"
      where
        !scope = contextScope $ edh'context ets
        !this = edh'scope'this scope

    mthValueRepr :: EdhHostProc
    mthValueRepr !exit !ets = case edh'obj'store this of
      HostStore dd ->
        exitEdh ets exit $
          EdhString $ "<host-value:" <> T.pack (show dd) <> ">"
      _ -> exitEdh ets exit $ EdhString "<bogus host-value>"
      where
        !scope = contextScope $ edh'context ets
        !this = edh'scope'this scope

    mthScopeRepr :: EdhHostProc
    mthScopeRepr !exit !ets =
      withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus scope object>") $
        \(scope :: Scope) ->
          exitEdh ets exit $
            EdhString $
              "<scope: "
                <> procedureName (edh'scope'proc scope)
                <> ">"

    mthScopeShow :: EdhHostProc
    mthScopeShow !exit !ets =
      withThisHostObj' ets (exitEdh ets exit $ EdhString "bogus scope object") $
        \(scope :: Scope) ->
          let !sp = edh'scope'proc scope
              !pd = edh'procedure'decl sp
           in exitEdh ets exit $
                EdhString $
                  "#scope: 📜 " <> procedureName sp
                    <> " 🔎 "
                    <> prettySrcLoc (edh'procedure'loc pd)

    mthScopeLexiLoc :: EdhHostProc
    mthScopeLexiLoc !exit !ets =
      withThisHostObj' ets (exitEdh ets exit $ EdhString "<bogus scope object>") $
        \(scope :: Scope) ->
          exitEdh ets exit $ EdhString $ prettySrcLoc $ edhScopeSrcLoc scope

    mthScopeAttrs :: EdhHostProc
    mthScopeAttrs !exit !ets =
      withThisHostObj' ets (throwEdh ets EvalError "bogus scope object") $
        \(scope :: Scope) ->
          (iopdSnapshot (edh'scope'entity scope) >>=) $
            exitEdh ets exit . EdhArgsPack . ArgsPack []

    mthScopeGet :: ArgsPack -> EdhHostProc
    mthScopeGet (ArgsPack !args !kwargs) !exit !ets =
      withThisHostObj' ets (throwEdh ets EvalError "bogus scope object") $
        \(scope :: Scope) -> do
          let !es = edh'scope'entity scope
              lookupAttrs ::
                [EdhValue] ->
                [(AttrKey, EdhValue)] ->
                [EdhValue] ->
                [(AttrKey, EdhValue)] ->
                (([EdhValue], [(AttrKey, EdhValue)]) -> STM ()) ->
                STM ()
              lookupAttrs rtnArgs rtnKwArgs [] [] !exit' =
                exit' (rtnArgs, rtnKwArgs)
              lookupAttrs rtnArgs rtnKwArgs [] ((n, v) : restKwArgs) !exit' =
                attrKeyFrom v $ \ !k -> do
                  !attrVal <- fromMaybe nil <$> iopdLookup k es
                  lookupAttrs
                    rtnArgs
                    ((n, attrVal) : rtnKwArgs)
                    []
                    restKwArgs
                    exit'
              lookupAttrs rtnArgs rtnKwArgs (v : restArgs) kwargs' !exit' =
                attrKeyFrom v $ \ !k -> do
                  !attrVal <- fromMaybe nil <$> iopdLookup k es
                  lookupAttrs
                    (attrVal : rtnArgs)
                    rtnKwArgs
                    restArgs
                    kwargs'
                    exit'
          lookupAttrs [] [] args (odToList kwargs) $ \case
            ([v], []) -> exitEdh ets exit v
            (rtnArgs, rtnKwArgs) ->
              exitEdh ets exit $
                EdhArgsPack $ ArgsPack (reverse rtnArgs) (odFromList rtnKwArgs)
      where
        attrKeyFrom :: EdhValue -> (AttrKey -> STM ()) -> STM ()
        attrKeyFrom
          (EdhExpr (ExprDefi _ (AttrExpr (DirectRef (AttrAddrSrc !addr _))) _) _)
          exit' = resolveEdhAttrAddr ets addr $ \ !key -> exit' key
        attrKeyFrom (EdhString attrName) !exit' = exit' $ AttrByName attrName
        attrKeyFrom (EdhSymbol sym) !exit' = exit' $ AttrBySym sym
        attrKeyFrom badVal _ =
          throwEdh ets UsageError $
            "invalid attribute reference type - " <> edhTypeNameOf badVal

    mthScopePut :: ArgsPack -> EdhHostProc
    mthScopePut (ArgsPack !args !kwargs) !exit !ets =
      withThisHostObj' ets (throwEdh ets EvalError "bogus scope object") $
        \(scope :: Scope) -> do
          let !es = edh'scope'entity scope
              putAttrs ::
                [EdhValue] ->
                [(AttrKey, EdhValue)] ->
                ([(AttrKey, EdhValue)] -> STM ()) ->
                STM ()
              putAttrs [] cumu !exit' = exit' cumu
              putAttrs (a : rest) cumu !exit' = case a of
                EdhPair (EdhString !k) !v ->
                  putAttrs rest ((AttrByName k, v) : cumu) exit'
                EdhPair (EdhSymbol !k) !v ->
                  putAttrs rest ((AttrBySym k, v) : cumu) exit'
                _ -> edhSimpleDesc ets a $ \ !badDesc ->
                  throwEdh ets UsageError $
                    "invalid key/value pair to put into a scope - "
                      <> badDesc
          putAttrs args [] $ \ !attrs -> do
            iopdUpdate (attrs ++ odToList kwargs) es
            exitEdh ets exit nil

    mthScopeEval :: "expression" !: ExprDefi -> EdhHostProc
    mthScopeEval
      (mandatoryArg -> ExprDefi _ !expr !src'loc)
      !exit
      !ets =
        withThisHostObj' ets (throwEdh ets EvalError "bogus scope object") $
          \(scope :: Scope) -> do
            -- eval specified expr with the original scope on top of current
            -- call stack
            !tipFrame <- newCallFrame scope src'loc
            let !ctx = edh'context ets
                !tip = edh'ctx'tip ctx
                !stack = edh'ctx'stack ctx
                !etsEval =
                  ets
                    { edh'context =
                        ctx
                          { edh'ctx'tip = tipFrame,
                            edh'ctx'stack = tip : stack,
                            edh'ctx'genr'caller = Nothing,
                            edh'ctx'match = true,
                            edh'ctx'pure = False,
                            edh'ctx'exp'target = Nothing,
                            edh'ctx'eff'target = Nothing
                          }
                    }
            runEdhTx etsEval $
              evalExpr expr $ \ !val _ets ->
                exitEdh ets exit $ edhDeCaseClose val

    mthScopeOuterGetter :: EdhHostProc
    mthScopeOuterGetter !exit !ets = case edh'obj'store this of
      HostStore !hsd -> case unwrapHostValue hsd of
        Nothing -> throwEdh ets EvalError "bogus scope object"
        Just (scope :: Scope) -> case outerScopeOf scope of
          Nothing -> exitEdh ets exit nil
          Just !outerScope ->
            edhMutCloneObj
              ets
              (edh'scope'that procScope)
              this
              (HostStore $ wrapHostValue outerScope)
              $ \ !outerScopeObj -> exitEdh ets exit $ EdhObject outerScopeObj
      _ -> exitEdh ets exit $ EdhString "bogus scope object"
      where
        !procScope = contextScope $ edh'context ets
        !this = edh'scope'this procScope

    -- this is called in case a ProgramHalt is constructed by Edh code
    haltAllocator !apk !exit _ = case apk of
      ArgsPack [] !kwargs | odNull kwargs -> createErr nil
      ArgsPack [v] !kwargs | odNull kwargs -> createErr v
      _ -> createErr $ EdhArgsPack apk
      where
        createErr !hv = do
          !hs <- pinHostValue $ toException $ ProgramHalt $ toDyn hv
          exit $ HostStore hs

    -- this is called in case a ThreadTerminate is constructed by Edh code
    thTermAllocator _ !exit _ = do
      !hs <- pinHostValue $ toException ThreadTerminate
      exit $ HostStore hs

    -- creating an IOError from Edh code
    ioErrAllocator apk@(ArgsPack !args !kwargs) !exit !ets = case args of
      [EdhString !m] | odNull kwargs -> createErr $ T.unpack m
      _ -> edhValueRepr ets (EdhArgsPack apk) $
        \ !repr -> createErr $ T.unpack repr
      where
        createErr !msg = do
          !hs <-
            pinHostValue $
              toException $ EdhIOError $ toException $ userError msg
          exit $ HostStore hs

    -- a peer error is most prolly created from Edh code
    peerErrAllocator !apk !exit _ = do
      !hs <- pinHostValue $ toException peerError
      exit $ HostStore hs
      where
        peerError = case apk of
          (ArgsPack [EdhString !peerSite, EdhString !details] !kwargs)
            | odNull kwargs -> EdhPeerError peerSite details
          _ -> EdhPeerError "<bogus-peer>" $ T.pack $ show apk

    -- creating a tagged Edh error from Edh code
    errAllocator !tag !apk !exit !ets = do
      !hs <- pinHostValue $ toException $ edhCreateError 0 ets tag apk
      exit $ HostStore hs

    mthErrRepr :: EdhHostProc
    mthErrRepr !exit !ets = case edh'obj'store errObj of
      HostStore !hsd -> case unwrapHostValue hsd of
        Just (exc :: SomeException) -> case edhKnownError exc of
          Just (ProgramHalt !dhv) -> case fromDynamic dhv of
            Just (val :: EdhValue) -> edhValueRepr ets val $ \ !repr ->
              exitEdh ets exit $ EdhString $ errClsName <> "(" <> repr <> ")"
            Nothing -> exitEdh ets exit $ EdhString $ errClsName <> "()"
          Just ThreadTerminate ->
            exitEdh ets exit $ EdhString "ThreadTerminate()"
          Just (EdhIOError !exc') ->
            exitEdh ets exit $
              EdhString $
                errClsName
                  <> "("
                  <> T.pack (show $ show exc')
                  <> ")"
          Just (EdhPeerError !peerSite !details) ->
            exitEdh ets exit $
              EdhString $
                errClsName
                  <> "("
                  <> T.pack (show peerSite)
                  <> ","
                  <> T.pack (show details)
                  <> ")"
          Just (EdhError _tag !msg _details _cc) ->
            if T.null msg
              then exitEdh ets exit $ EdhString $ errClsName <> "()"
              else
                exitEdh ets exit $
                  EdhString $
                    errClsName
                      <> "(`"
                      <> msg
                      <> "`)"
          _ -> exitEdh ets exit $ EdhString $ errClsName <> "()"
        Nothing -> exitEdh ets exit $ EdhString $ errClsName <> "()"
      _ -> exitEdh ets exit $ EdhString $ errClsName <> "()"
      where
        !scope = contextScope $ edh'context ets
        !errObj = edh'scope'this scope
        !endErr = edh'scope'that scope
        !errClsName = objClassName endErr

    mthErrShow :: EdhHostProc
    mthErrShow !exit !ets = case edh'obj'store errObj of
      HostStore !hsd -> case unwrapHostValue hsd of
        Just (exc :: SomeException) -> case edhKnownError exc of
          Just err@(EdhError _errTag _errMsg !details _cc) -> do
            let !detailsText = case fromDynamic details of
                  Just EdhNil -> ""
                  Just _ -> "\n * with more detailed data."
                  _ -> ""
            exitEdh ets exit $ EdhString $ T.pack (show err) <> detailsText
          _ ->
            exitEdh ets exit $
              EdhString $
                errClsName <> ": "
                  <> T.pack
                    (show exc)
        _ ->
          exitEdh ets exit $
            EdhString $
              "bogus error object of: "
                <> errClsName
      _ ->
        exitEdh ets exit $ EdhString $ "bogus error object of: " <> errClsName
      where
        !errObj = edh'scope'this $ contextScope $ edh'context ets
        !errClsName = objClassName errObj

    mthErrDesc :: EdhHostProc
    mthErrDesc !exit !ets = case edh'obj'store errObj of
      HostStore !hsd -> case unwrapHostValue hsd of
        Just (exc :: SomeException) -> case edhKnownError exc of
          Just err@(EdhError _errTag _errMsg !details _errCtx) ->
            case fromDynamic details of
              Just EdhNil -> exitEdh ets exit $ EdhString $ T.pack (show err)
              Just !detailsVal -> edhValueStr ets detailsVal $ \ !detailsStr ->
                exitEdh ets exit $
                  EdhString $
                    T.pack (show err)
                      <> "\n * details:\n"
                      <> detailsStr
              _ -> exitEdh ets exit $ EdhString $ T.pack (show err)
          _ ->
            exitEdh ets exit $
              EdhString $ errClsName <> ": " <> T.pack (show exc)
        _ ->
          exitEdh ets exit $
            EdhString $ "bogus error object of: " <> errClsName
      _ ->
        exitEdh ets exit $
          EdhString $ "bogus error object of: " <> errClsName
      where
        !errObj = edh'scope'this $ contextScope $ edh'context ets
        !errClsName = objClassName errObj

    mthErrCtxGetter :: EdhHostProc
    mthErrCtxGetter !exit !ets = case edh'obj'store errObj of
      HostStore !hsd -> case unwrapHostValue hsd of
        Just (exc :: SomeException) -> case edhKnownError exc of
          Just (EdhError _errTag _errMsg _details !errCtx) ->
            exitEdh ets exit $ EdhString errCtx
          _ -> exitEdh ets exit nil
        _ -> exitEdh ets exit nil
      _ -> exitEdh ets exit nil
      where
        !errObj = edh'scope'this $ contextScope $ edh'context ets

    mthErrMsgGetter :: EdhHostProc
    mthErrMsgGetter !exit !ets = case edh'obj'store errObj of
      HostStore !hsd -> case unwrapHostValue hsd of
        Just (exc :: SomeException) -> case edhKnownError exc of
          Just (EdhError _errTag !errMsg _errDetails _errCtx) ->
            exitEdh ets exit $ EdhString errMsg
          _ -> exitEdh ets exit nil
        _ -> exitEdh ets exit nil
      _ -> exitEdh ets exit nil
      where
        !errObj = edh'scope'this $ contextScope $ edh'context ets

    mthErrDetailsGetter :: EdhHostProc
    mthErrDetailsGetter !exit !ets = case edh'obj'store errObj of
      HostStore !hsd -> case unwrapHostValue hsd of
        Just (exc :: SomeException) -> case edhKnownError exc of
          Just (EdhError _errTag _errMsg !errDetails _errCtx) ->
            case fromDynamic errDetails of
              Just (detailsValue :: EdhValue) -> exitEdh ets exit detailsValue
              _ -> exitEdh ets exit nil
          _ -> exitEdh ets exit nil
        _ -> exitEdh ets exit nil
      _ -> exitEdh ets exit nil
      where
        !errObj = edh'scope'this $ contextScope $ edh'context ets

    moduleAllocator ::
      "__name__" ?: Text ->
      "__file__" ?: Text ->
      RestKwArgs ->
      EdhObjectAllocator
    moduleAllocator
      (defaultArg "__anonymous__" -> !moduName)
      (defaultArg ("<on-the-fly:" <> moduName <> ">") -> !moduFile)
      !extraArts
      !exit
      _ets =
        exit . HashStore =<< iopdFromList moduArts
        where
          moduArts =
            odToList extraArts
              ++ [ (AttrByName "__name__", EdhString moduName),
                   (AttrByName "__file__", EdhString moduFile)
                 ]

    mthModuRepr :: EdhHostProc
    mthModuRepr !exit !ets = do
      !name <- lookupEdhSelfAttr this (AttrByName "__name__")
      edhValueStr ets name $ \ !nameStr ->
        exitEdh ets exit $ EdhString $ "<module: " <> nameStr <> ">"
      where
        !this = edh'scope'this $ contextScope $ edh'context ets

    mthModuShow :: EdhHostProc
    mthModuShow !exit !ets = do
      !name <- lookupEdhSelfAttr this (AttrByName "__name__")
      !file <- lookupEdhSelfAttr this (AttrByName "__file__")
      edhValueStr ets name $ \ !nameStr -> edhValueStr ets file $ \ !fileStr ->
        exitEdh ets exit $
          EdhString $
            " ** module: "
              <> nameStr
              <> "\n  * loaded from: "
              <> fileStr
      where
        !this = edh'scope'this $ contextScope $ edh'context ets

    mthModuCall :: "moduScript" !: ExprDefi -> EdhHostProc
    mthModuCall (mandatoryArg -> moduScript@(ExprDefi _ _ srcLoc)) !exit !ets =
      objectScope thisModu >>= \ !moduScope -> do
        !tipFrame <- newCallFrame moduScope srcLoc
        let ctxModu = ctx {edh'ctx'tip = tipFrame}
            etsModu = ets {edh'context = ctxModu}
        runEdhTx etsModu $
          evalExprDefi moduScript $ \_ _ets ->
            exitEdh ets exit $ EdhObject thisModu
      where
        !ctx = edh'context ets
        !thisModu = edh'scope'this $ contextScope ctx

declareEdhOperators ::
  EdhWorld -> OpDeclLoc -> [(OpSymbol, OpFixity, Precedence)] -> IO ()
declareEdhOperators !world !declLoc !opps = do
  baseOD@(GlobalOpDict !decls !quaint'ops) <- readTVarIO wops
  let chkCompatible :: (OpSymbol, OpFixity, Precedence) -> STM ()
      chkCompatible (!sym, !fixty, !precedence) = case Map.lookup sym decls of
        Nothing -> return ()
        Just (prevFixity, prevPrec, prevDeclLoc) ->
          if prevPrec /= precedence
            then
              throwSTM $
                EdhError
                  UsageError
                  ( "precedence change from "
                      <> T.pack (show prevPrec)
                      <> " (declared at "
                      <> prevDeclLoc
                      <> ") to "
                      <> T.pack (show precedence)
                      <> " (declared at "
                      <> T.pack (show declLoc)
                      <> ") for operator: "
                      <> sym
                  )
                  (toDyn nil)
                  "<edh>"
            else case fixty of
              Infix -> return ()
              _ ->
                when (fixty /= prevFixity) $
                  throwSTM $
                    EdhError
                      UsageError
                      ( "fixity change from "
                          <> T.pack (show prevFixity)
                          <> " (declared at "
                          <> prevDeclLoc
                          <> ") to "
                          <> T.pack (show fixty)
                          <> " (declared at "
                          <> T.pack (show declLoc)
                          <> ") for operator: "
                          <> sym
                      )
                      (toDyn nil)
                      "<edh>"
      decls' = Map.fromList $
        flip fmap opps $ \(sym, fixity, precedence) ->
          (sym, (fixity, precedence, declLoc))
  atomically $ sequence_ $ chkCompatible <$> opps
  mergeOpDict wops baseOD $
    GlobalOpDict (Map.union decls decls') $
      L.sort $
        quaint'ops
          ++ [ sym
               | (sym, _fixty, _precedence) <- opps,
                 contain'nonstd'op'char sym
             ]
  where
    !wops = edh'world'operators world
    contain'nonstd'op'char :: OpSymbol -> Bool
    contain'nonstd'op'char sym = isJust $ T.find (not . isOperatorChar) sym

haltEdhProgram :: EdhTxExit EdhValue
haltEdhProgram !hv !ets =
  edhWrapException (Just ets) (toException $ ProgramHalt $ toDyn hv)
    >>= \ !exo -> edhThrow ets $ EdhObject exo
  where
    !edhWrapException =
      edh'exception'wrapper (edh'prog'world $ edh'thread'prog ets)

terminateEdhThread :: EdhTx
terminateEdhThread !ets =
  edhWrapException (Just ets) (toException ThreadTerminate)
    >>= \ !exo -> edhThrow ets $ EdhObject exo
  where
    !edhWrapException =
      edh'exception'wrapper (edh'prog'world $ edh'thread'prog ets)

runEdhProgram :: EdhWorld -> EdhTx -> IO (Either EdhError EdhValue)
runEdhProgram !world !prog =
  tryJust edhKnownError $ runEdhProgram' world prog

runEdhProgram' :: EdhWorld -> EdhTx -> IO EdhValue
runEdhProgram' !world !prog = do
  !haltResult <- newEmptyTMVarIO
  driveEdhProgram haltResult world prog
  atomically (tryReadTMVar haltResult) >>= \case
    Nothing -> return nil
    Just (Right v) -> return v
    Just (Left e) -> throwIO e

type EdhModulePreparation = EdhThreadState -> STM () -> STM ()

edhModuleAsIs :: EdhModulePreparation
edhModuleAsIs _ets !exit = exit

installEdhModule :: EdhWorld -> Text -> EdhModulePreparation -> IO Object
installEdhModule !world !moduName !preInstall = do
  !modu <-
    createEdhModule world moduName $ T.unpack $ "<host:" <> moduName <> ">"
  void $
    runEdhProgram' world $ \ !ets ->
      moduleContext world modu >>= \ !moduCtx ->
        preInstall ets {edh'context = moduCtx} $ do
          !moduSlot <- newTVar $ ModuLoaded modu
          !moduMap <- takeTMVar (edh'world'modules world)
          putTMVar (edh'world'modules world) $
            Map.insert (HostModule moduName) moduSlot moduMap
  return modu

runEdhModule ::
  EdhWorld ->
  FilePath ->
  EdhModulePreparation ->
  IO (Either EdhError EdhValue)
runEdhModule !world !impPath !preRun =
  tryJust edhKnownError $ runEdhModule' world impPath preRun

runEdhModule' :: EdhWorld -> FilePath -> EdhModulePreparation -> IO EdhValue
runEdhModule' !world !impPath !preRun =
  let ?fileExt = ".edh"
   in locateEdhMainModule impPath >>= \case
        Left !err ->
          throwIO $ EdhError PackageError err (toDyn nil) "<run-modu>"
        Right !moduFile -> do
          !fileContent <- B.readFile moduFile
          case streamDecodeUtf8With lenientDecode fileContent of
            Some !moduSource _ _ -> do
              !modu <- createEdhModule world (T.pack impPath) moduFile
              runEdhProgram' world $ \ !etsMain ->
                moduleContext world modu >>= \ !moduCtx ->
                  let !etsModu = etsMain {edh'context = moduCtx}
                   in preRun etsModu $
                        runEdhTx etsModu $
                          evalEdh (T.pack moduFile) moduSource endOfEdh

runEdhFile :: EdhWorld -> FilePath -> IO (Either EdhError EdhValue)
runEdhFile !world !edhFile =
  tryJust edhKnownError $ runEdhFile' world edhFile

runEdhFile' :: EdhWorld -> FilePath -> IO EdhValue
runEdhFile' !world !edhFile = do
  !absFile <- canonicalizePath edhFile
  !fileContent <- B.readFile absFile
  case streamDecodeUtf8With lenientDecode fileContent of
    Some !moduSource _ _ -> do
      !modu <- createEdhModule world "__main__" absFile
      runEdhProgram' world $ \ !etsMain ->
        moduleContext world modu >>= \ !moduCtx ->
          let !etsModu = etsMain {edh'context = moduCtx}
           in runEdhTx etsModu $ evalEdh (T.pack absFile) moduSource endOfEdh
