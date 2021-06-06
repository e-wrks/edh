module Language.Edh.Runtime where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
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
import Data.Unique
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Args
import Language.Edh.Control
import Language.Edh.CoreLang
import Language.Edh.Evaluate
import Language.Edh.IOPD
import Language.Edh.InterOp
import Language.Edh.PkgMan
import Language.Edh.RtTypes
import Language.Edh.Utils
import System.Environment
import System.Posix.Signals
import Prelude

createEdhWorld :: EdhConsole -> IO EdhWorld
createEdhWorld !console = do
  -- the meta class
  !idMeta <- newUnique
  !hsMeta <- atomically iopdEmpty
  !ssMeta <- newTVarIO []
  !mroMeta <- newTVarIO [] -- no super class, and self is not stored

  -- the root object and root scope
  !idRoot <- newUnique
  !hsRoot <-
    atomically $
      iopdFromList [(AttrByName "__name__", EdhString "<root>")]
  !ssRoot <- newTVarIO []

  -- the sandbox object and sandbox scope
  !idSandbox <- newUnique
  !hsSandbox <-
    atomically $
      iopdFromList [(AttrByName "__name__", EdhString "<sandbox>")]
  !ssSandbox <- newTVarIO []
  !mroSandbox <- newTVarIO [] -- no super class, and self is not stored

  -- the namespace class, root object is a special instance of namespace class
  !idNamespace <- newUnique
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
          (HostDecl phantomHostProc)
      rootObj = Object idRoot (HashStore hsRoot) nsClassObj ssRoot

      sandboxScope = Scope hsSandbox sandboxObj sandboxObj sandboxProc []
      sandboxProc =
        ProcDefi
          idSandbox
          (AttrByName "<sandbox>")
          sandboxScope
          (DocCmt ["the sandbox namespace"])
          (HostDecl phantomHostProc)
      sandboxObj =
        Object idSandbox (HashStore hsSandbox) sandboxClassObj ssSandbox
      sandboxClass = Class sandboxProc hsSandbox phantomAllocator mroSandbox
      sandboxClassObj =
        Object idSandbox (ClassStore sandboxClass) metaClassObj ssSandbox

      metaProc =
        ProcDefi
          idMeta
          (AttrByName "class")
          rootScope
          (DocCmt ["the meta class"])
          (HostDecl phantomHostProc)
      metaClass = Class metaProc hsMeta phantomAllocator mroMeta
      metaClassObj = Object idMeta (ClassStore metaClass) metaClassObj ssMeta

      nsProc =
        ProcDefi
          idNamespace
          (AttrByName "<namespace>")
          rootScope
          (DocCmt ["the namespace class"])
          (HostDecl phantomHostProc)
      nsClass = Class nsProc hsNamespace phantomAllocator mroNamespace
      nsClassObj =
        Object idNamespace (ClassStore nsClass) metaClassObj ssNamespace

  atomically $
    (flip iopdUpdate hsMeta =<<) $
      sequence
      -- todo more static attrs for class objects here
      $
        [ (AttrByName nm,) <$> mkHostProc rootScope EdhMethod nm hp
          | (nm, hp) <-
              [ ("__repr__", wrapHostProc mthClassRepr),
                ("__show__", wrapHostProc mthClassShow)
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
        throwEdh
          ets
          UsageError
          "you can not create a host value from script"
  !clsHostValue <-
    atomically $
      mkHostClass'
        rootScope
        "<host-value>"
        (allocEdhObj hostValueAllocator)
        hsHostValue
        []
  let edhWrapValue :: Dynamic -> STM Object
      edhWrapValue !dd = do
        !idHostValue <- unsafeIOToSTM newUnique
        !ss <- newTVar []
        return
          Object
            { edh'obj'ident = idHostValue,
              edh'obj'store = HostStore dd,
              edh'obj'class = clsHostValue,
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
          Just !obj ->
            objectScope obj
              >>= \ !objScope -> exit Nothing $ HostStore $ toDyn objScope
          Nothing ->
            exit Nothing $ HostStore $ toDyn $ contextScope $ edh'context ets
  !clsScope <-
    atomically $
      mkHostClass' rootScope "scope" (allocEdhObj scopeAllocator) hsScope []
  let edhWrapScope :: Scope -> STM Object
      edhWrapScope !scope = do
        !idScope <- unsafeIOToSTM newUnique
        !ss <- newTVar []
        return
          Object
            { edh'obj'ident = idScope,
              edh'obj'store = HostStore $ toDyn scope,
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

  let edhWrapException :: SomeException -> STM Object
      edhWrapException !exc = do
        !uidErr <- unsafeIOToSTM newUnique
        !supersErr <- newTVar []
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
            return $
              Object
                uidErr
                (HostStore $ toDyn $ toException err)
                clsErr
                supersErr
          Nothing ->
            return $
              Object
                uidErr
                (HostStore $ toDyn $ toException $ EdhIOError exc)
                clsIOError
                supersErr

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
              clsUsageError
            ]
      ]
      hsRoot

  -- the `module` class
  !hsModuCls <-
    atomically $
      (iopdFromList =<<) $
        sequence $
          [ (AttrByName nm,) <$> mkHostProc rootScope EdhMethod nm hp
            | (nm, hp) <-
                [ ("__repr__", wrapHostProc mthModuClsRepr),
                  ("__show__", wrapHostProc mthModuClsShow)
                ]
          ]
  !clsModule <-
    atomically $
      mkHostClass' rootScope "module" (allocEdhObj moduleAllocator) hsModuCls []
  atomically $ iopdUpdate [(AttrByName "module", EdhObject clsModule)] hsRoot

  -- operator precedence dict
  !opPD <- newTMVarIO $ GlobalOpDict Map.empty []

  -- the meta host module
  !metaModu <-
    newTVarIO $
      ModuLoaded $
        Object
          { edh'obj'ident = idRoot,
            edh'obj'store = HashStore hsRoot,
            edh'obj'class = clsModule,
            edh'obj'supers = ssRoot
          }

  -- the container of loaded modules
  !modus <- newTMVarIO $ Map.fromList [("batteries/meta", metaModu)]

  !trapReq <- newIORef 0
  -- record a trap request on SIGQUIT
  lookupEnv "EDH_TRAP_SIGQUIT" >>= \case
    Nothing -> pure ()
    Just "" -> pure ()
    Just "0" -> pure ()
    Just "NO" -> pure ()
    Just {} ->
      addSignalHandler keyboardTermination $ modifyIORef' trapReq (+ 1)

  -- assembly the world with pieces prepared above
  let !world =
        EdhWorld
          { edh'world'root = rootScope,
            edh'world'sandbox = sandboxScope,
            edh'world'operators = opPD,
            edh'world'modules = modus,
            edh'world'console = console,
            edh'value'wrapper = edhWrapValue,
            edh'scope'wrapper = edhWrapScope,
            edh'exception'wrapper = edhWrapException,
            edh'module'class = clsModule,
            edh'trap'request = trapReq
          }

  return world
  where
    phantomAllocator :: ArgsPack -> EdhObjectAllocator
    phantomAllocator _ _ !ets =
      throwEdh ets EvalError "bug: allocating phantom object"
    phantomHostProc :: ArgsPack -> EdhHostProc
    phantomHostProc _apk _exit =
      throwEdhTx EvalError "bug: calling phantom procedure"

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
          EdhString $
            "class: "
              <> procedureName
                (edh'class'proc cls)
      _ -> exitEdh ets exit $ EdhString "<bogus-class>"
      where
        !clsObj = edh'scope'that $ contextScope $ edh'context ets

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
    mthNsRepr !exit !ets = exitEdh ets exit . EdhString =<< nsRepr
      where
        !scope = contextScope $ edh'context ets
        nsRepr :: STM Text
        nsRepr = case edh'obj'store $ edh'scope'this scope of
          HashStore !hs ->
            iopdLookup (AttrByName "__name__") hs >>= \case
              Just (EdhString !nsn) -> return $ "<namespace: " <> nsn <> ">"
              Just (EdhSymbol (Symbol _ !nssr)) ->
                return $ "<namespace: " <> nssr <> ">"
              Nothing -> return "<namespace>"
              _ -> return "<bogus-namespace>"
          _ -> return "<bogus-namespace>"

    mthNsShow :: EdhHostProc
    mthNsShow !exit !ets = exitEdh ets exit . EdhString =<< nsShow
      where
        !scope = contextScope $ edh'context ets
        nsShow :: STM Text
        nsShow = case edh'obj'store $ edh'scope'this scope of
          HashStore !hs ->
            iopdLookup (AttrByName "__name__") hs >>= \case
              Just (EdhString !nsn) ->
                return $ "It's a namespace named `" <> nsn <> "`"
              Just (EdhSymbol (Symbol _ !nssr)) ->
                return $ "It's a symbolic namespace named `" <> nssr <> "`"
              Nothing -> return "It's an anonymous namespace"
              _ -> return "It's a bogus-namespace"
          _ -> return "It's a bogus-namespace"

    mthNsDesc :: EdhHostProc
    mthNsDesc !exit !ets = exitEdh ets exit . EdhString =<< nsDesc
      where
        !scope = contextScope $ edh'context ets
        nsDesc :: STM Text
        -- TODO elaborate the informatiion
        nsDesc = case edh'obj'store $ edh'scope'this scope of
          HashStore !hs ->
            iopdLookup (AttrByName "__name__") hs >>= \case
              Just (EdhString !nsn) ->
                return $ "It's a namespace named `" <> nsn <> "`"
              Just (EdhSymbol (Symbol _ !nssr)) ->
                return $ "It's a symbolic namespace named `" <> nssr <> "`"
              Nothing -> return "It's an anonymous namespace"
              _ -> return "It's a bogus-namespace"
          _ -> return "It's a bogus-namespace"

    mthValueRepr :: EdhHostProc
    mthValueRepr !exit !ets = case edh'obj'store this of
      HostStore (Dynamic !tr _) ->
        exitEdh ets exit $
          EdhString $ "<host-value:< " <> T.pack (show tr) <> ">>"
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
          (EdhExpr _ (AttrExpr (DirectRef (AttrAddrSrc !addr _))) _)
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
                _ -> edhValueDesc ets a $ \ !badDesc ->
                  throwEdh ets UsageError $
                    "invalid key/value pair to put into a scope - "
                      <> badDesc
          putAttrs args [] $ \ !attrs -> do
            iopdUpdate (attrs ++ odToList kwargs) es
            exitEdh ets exit nil

    mthScopeEval :: "expression" !: EdhValue -> "srcName" ?: Text -> EdhHostProc
    mthScopeEval
      (mandatoryArg -> !exprVal)
      (defaultArg "<ad-hoc>" -> !srcName)
      !exit
      !ets =
        withThisHostObj' ets (throwEdh ets EvalError "bogus scope object") $
          \(scope :: Scope) -> do
            -- eval specified expr with the original scope on top of current
            -- call stack
            let !ctx = edh'context ets
                !etsEval =
                  ets
                    { edh'context =
                        ctx
                          { edh'ctx'tip =
                              EdhCallFrame
                                scope
                                (SrcLoc (SrcDoc srcName) zeroSrcRange)
                                defaultEdhExcptHndlr,
                            edh'ctx'stack = edh'ctx'tip ctx : edh'ctx'stack ctx,
                            edh'ctx'genr'caller = Nothing,
                            edh'ctx'match = true,
                            edh'ctx'pure = False,
                            edh'ctx'exporting = False,
                            edh'ctx'eff'defining = False
                          }
                    }
            case exprVal of
              EdhExpr _ !expr _ ->
                runEdhTx etsEval $
                  evalExpr expr $ \ !val _ets ->
                    exitEdh ets exit $ edhDeCaseClose val
              !badExpr -> edhValueDesc ets badExpr $ \ !badDesc ->
                throwEdh ets EvalError $ "not an expr: " <> badDesc

    mthScopeOuterGetter :: EdhHostProc
    mthScopeOuterGetter !exit !ets = case edh'obj'store this of
      HostStore !hsd -> case fromDynamic hsd of
        Nothing -> throwEdh ets EvalError "bogus scope object"
        Just (scope :: Scope) -> case outerScopeOf scope of
          Nothing -> exitEdh ets exit nil
          Just !outerScope ->
            edhMutCloneObj
              ets
              this
              (edh'scope'that procScope)
              (HostStore $ toDyn outerScope)
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
        createErr !hv =
          exit Nothing $
            HostStore $ toDyn $ toException $ ProgramHalt $ toDyn hv

    -- this is called in case a ThreadTerminate is constructed by Edh code
    thTermAllocator _ !exit _ =
      exit Nothing $ HostStore $ toDyn $ toException ThreadTerminate

    -- creating an IOError from Edh code
    ioErrAllocator apk@(ArgsPack !args !kwargs) !exit !ets = case args of
      [EdhString !m] | odNull kwargs -> createErr $ T.unpack m
      _ -> edhValueRepr ets (EdhArgsPack apk) $
        \ !repr -> createErr $ T.unpack repr
      where
        createErr !msg =
          exit Nothing $
            HostStore $
              toDyn $
                toException $
                  EdhIOError $
                    toException $
                      userError msg

    -- a peer error is most prolly created from Edh code
    peerErrAllocator !apk !exit _ =
      exit Nothing $
        HostStore $
          toDyn $
            toException
              peerError
      where
        peerError = case apk of
          (ArgsPack [EdhString !peerSite, EdhString !details] !kwargs)
            | odNull kwargs -> EdhPeerError peerSite details
          _ -> EdhPeerError "<bogus-peer>" $ T.pack $ show apk

    -- creating a tagged Edh error from Edh code
    errAllocator !tag !apk !exit !ets =
      exit Nothing $
        HostStore $ toDyn $ toException $ edhCreateError 0 ets tag apk

    mthErrRepr :: EdhHostProc
    mthErrRepr !exit !ets = case edh'obj'store errObj of
      HostStore !hsd -> case fromDynamic hsd of
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
      HostStore !hsd -> case fromDynamic hsd of
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
      HostStore !hsd -> case fromDynamic hsd of
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
      HostStore !hsd -> case fromDynamic hsd of
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
      HostStore !hsd -> case fromDynamic hsd of
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
      HostStore !hsd -> case fromDynamic hsd of
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
      "__name__" !: Text ->
      "__path__" ?: Text ->
      "__file__" ?: Text ->
      RestKwArgs ->
      EdhObjectAllocator
    moduleAllocator
      (mandatoryArg -> !moduName)
      (defaultArg "<ad-hoc>" -> !moduPath)
      (defaultArg "<on-the-fly>" -> !moduFile)
      !extraArts
      !exit
      _ets =
        exit Nothing . HashStore =<< iopdFromList moduArts
        where
          moduArts =
            odToList extraArts
              ++ [ (AttrByName "__name__", EdhString moduName),
                   (AttrByName "__path__", EdhString moduPath),
                   (AttrByName "__file__", EdhString moduFile)
                 ]

    mthModuClsRepr :: EdhHostProc
    mthModuClsRepr !exit !ets = do
      !path <- lookupEdhSelfAttr this (AttrByName "__path__")
      edhValueStr ets path $ \ !pathStr ->
        exitEdh ets exit $ EdhString $ "<module: " <> pathStr <> ">"
      where
        !this = edh'scope'this $ contextScope $ edh'context ets

    mthModuClsShow :: EdhHostProc
    mthModuClsShow !exit !ets = do
      !path <- lookupEdhSelfAttr this (AttrByName "__path__")
      !file <- lookupEdhSelfAttr this (AttrByName "__file__")
      edhValueStr ets path $ \ !pathStr -> edhValueStr ets file $ \ !fileStr ->
        exitEdh ets exit $
          EdhString $
            " ** module: "
              <> pathStr
              <> "\n  * loaded from: "
              <> fileStr
      where
        !this = edh'scope'this $ contextScope $ edh'context ets

declareEdhOperators ::
  EdhWorld -> OpDeclLoc -> [(OpSymbol, OpFixity, Precedence)] -> STM ()
declareEdhOperators !world !declLoc !opps = do
  GlobalOpDict !decls !quaint'ops <- takeTMVar wops
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
  sequence_ $ chkCompatible <$> opps
  putTMVar wops $
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

haltEdhProgram :: EdhThreadState -> EdhValue -> STM ()
haltEdhProgram !ets !hv =
  edhWrapException (toException $ ProgramHalt $ toDyn hv)
    >>= \ !exo -> edhThrow ets $ EdhObject exo
  where
    !edhWrapException =
      edh'exception'wrapper (edh'prog'world $ edh'thread'prog ets)

terminateEdhThread :: EdhThreadState -> STM ()
terminateEdhThread !ets =
  edhWrapException (toException ThreadTerminate)
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
  liftIO (atomically $ tryReadTMVar haltResult) >>= \case
    Nothing -> return nil
    Just (Right v) -> return v
    Just (Left e) -> throwIO e

createEdhModule ::
  EdhWorld -> Text -> ModuleId -> String -> IO Object
createEdhModule !world !moduName !moduId !srcName =
  atomically $ edhCreateModule world moduName moduId srcName

type EdhModulePreparation = EdhThreadState -> STM () -> STM ()

edhModuleAsIs :: EdhModulePreparation
edhModuleAsIs _ets !exit = exit

installEdhModule ::
  EdhWorld -> ModuleId -> EdhModulePreparation -> IO Object
installEdhModule !world !moduId !preInstall = do
  !modu <- createEdhModule world moduId moduId "<host-module>"
  void $
    runEdhProgram' world $ \ !ets ->
      moduleContext world modu >>= \ !moduCtx ->
        preInstall ets {edh'context = moduCtx} $ do
          !moduSlot <- newTVar $ ModuLoaded modu
          !moduMap <- takeTMVar (edh'world'modules world)
          putTMVar (edh'world'modules world) $
            Map.insert moduId moduSlot moduMap
  return modu

installedEdhModule :: EdhWorld -> ModuleId -> IO (Maybe Object)
installedEdhModule !world !moduId =
  atomically $
    tryReadTMVar (edh'world'modules world) >>= \case
      Nothing -> return Nothing
      Just !mm -> case Map.lookup moduId mm of
        Nothing -> return Nothing
        Just !moduSlotVar ->
          readTVar moduSlotVar >>= \case
            ModuLoaded !modu -> return $ Just modu
            ModuLoading !loadScope _ ->
              return $ Just $ edh'scope'this loadScope
            _ -> return Nothing

runEdhModule ::
  EdhWorld ->
  FilePath ->
  EdhModulePreparation ->
  IO (Either EdhError EdhValue)
runEdhModule !world !impPath !preRun =
  tryJust edhKnownError $ runEdhModule' world impPath preRun

runEdhModule' ::
  EdhWorld -> FilePath -> EdhModulePreparation -> IO EdhValue
runEdhModule' !world !impPath !preRun =
  locateEdhMainModule impPath >>= \case
    Left !err -> throwIO $ EdhError PackageError err (toDyn nil) "<run-modu>"
    Right (!moduName, !nomPath, !moduFile) -> do
      !fileContent <- B.readFile moduFile
      case streamDecodeUtf8With lenientDecode fileContent of
        Some !moduSource _ _ -> runEdhProgram' world $ \ !etsMain ->
          let !moduId = T.pack nomPath
           in edhCreateModule world moduName moduId moduFile >>= \ !modu ->
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
  !fileContent <- B.readFile edhFile
  case streamDecodeUtf8With lenientDecode fileContent of
    Some !moduSource _ _ -> runEdhProgram' world $ \ !etsMain ->
      edhCreateModule world "__main__" "__main__" edhFile >>= \ !modu ->
        moduleContext world modu >>= \ !moduCtx ->
          let !etsModu = etsMain {edh'context = moduCtx}
           in runEdhTx etsModu $ evalEdh (T.pack edhFile) moduSource endOfEdh
