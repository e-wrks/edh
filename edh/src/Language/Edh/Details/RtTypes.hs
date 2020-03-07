
module Language.Edh.Details.RtTypes where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )
import           System.IO.Unsafe

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader

-- import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Foldable
import           Data.Unique
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Hashable
import qualified Data.HashMap.Strict           as Map
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE


import           Text.Megaparsec

import           Data.Lossless.Decimal         as D

import           Language.Edh.Control


-- | A dict in Edh is neither an object nor an entity, but just a
-- mutable associative array.
data Dict = Dict !Unique !(TVar DictStore)
instance Eq Dict where
  Dict x'u _ == Dict y'u _ = x'u == y'u
instance Ord Dict where
  compare (Dict x'u _) (Dict y'u _) = compare x'u y'u
instance Hashable Dict where
  hashWithSalt s (Dict u _) = hashWithSalt s u
instance Show Dict where
  show (Dict _ d) = showEdhDict ds where ds = unsafePerformIO $ readTVarIO d
type ItemKey = EdhValue
type DictStore = Map.HashMap EdhValue EdhValue

showEdhDict :: DictStore -> String
showEdhDict ds = if Map.null ds
  then "{,}" -- make it obvious this is an empty dict
  else -- advocate trailing comma here
    "{ "
    ++ concat [ show k ++ ":" ++ show v ++ ", " | (k, v) <- Map.toList ds ]
    ++ "}"

-- | setting to `nil` value means deleting the item by the specified key
setDictItem :: ItemKey -> EdhValue -> DictStore -> DictStore
setDictItem !k v !ds =
  if v == EdhNil then Map.delete k ds else Map.insert k v ds

toPairList :: DictStore -> [EdhValue]
toPairList d = (<$> Map.toList d) $ \(k, v) -> EdhPair k v

edhDictFromEntity :: Entity -> STM Dict
edhDictFromEntity ent = do
  u  <- unsafeIOToSTM newUnique
  em <- readTVar $ entity'store ent
  (Dict u <$>) $ newTVar $ Map.fromList
    [ (attrKeyValue k, v) | (k, v) <- Map.toList em ]

-- | An entity in Edh is the backing storage for a scope, with possibly 
-- an object mounted to it with one class and many supers
--
-- An entity has attributes associated by 'AttrKey'.
data Entity = Entity {
    entity'ident :: !Unique
    , entity'store :: !(TVar EntityStore)
  }
instance Eq Entity where
  Entity x'u _ == Entity y'u _ = x'u == y'u
instance Ord Entity where
  compare (Entity x'u _) (Entity y'u _) = compare x'u y'u
instance Hashable Entity where
  hashWithSalt s (Entity u _) = hashWithSalt s u

type EntityStore = Map.HashMap AttrKey EdhValue
data AttrKey = AttrByName !AttrName | AttrBySym !Symbol
    deriving (Eq, Ord, Show)
instance Hashable AttrKey where
  hashWithSalt s (AttrByName name) =
    s `hashWithSalt` (0 :: Int) `hashWithSalt` name
  hashWithSalt s (AttrBySym sym) =
    s `hashWithSalt` (1 :: Int) `hashWithSalt` sym

createEntity :: EntityStore -> STM Entity
createEntity !es = do
  u <- unsafeIOToSTM newUnique
  Entity u <$> newTVar es

-- | setting to `nil` value means deleting the attribute by the specified key
setEntityAttr :: AttrKey -> EdhValue -> EntityStore -> EntityStore
setEntityAttr !k v !es =
  if v == EdhNil then Map.delete k es else Map.insert k v es

type AttrName = Text

attrKeyValue :: AttrKey -> EdhValue
attrKeyValue (AttrByName nm ) = EdhString nm
attrKeyValue (AttrBySym  sym) = EdhSymbol sym


-- | A symbol can stand in place of an alphanumeric name, used to
-- address an attribute from an object entity, but symbols are 
-- private to its owning scope, can not be imported from out side
-- of the scope, thus serves encapsulation purpose in object
-- structure designs.
--
-- And symbol values reside in a lexical outer scope are available
-- to its lexical inner scopes, e.g. a symbol bound to a module is
-- available to all procedures defined in the module, and a symbol
-- bound within a class procedure is available to all its methods
-- as well as nested classes.
data Symbol = Symbol !Unique !Bool !Text
instance Eq Symbol where
  Symbol x'u _ _ == Symbol y'u _ _ = x'u == y'u
instance Ord Symbol where
  compare (Symbol x'u _ _) (Symbol y'u _ _) = compare x'u y'u
instance Hashable Symbol where
  hashWithSalt s (Symbol u _ _) = hashWithSalt s u
instance Show Symbol where
  show (Symbol _ _ sym) = T.unpack sym
mkSymbol :: String -> Bool -> STM Symbol
mkSymbol !description !nullSemantic = do
  !u <- unsafeIOToSTM newUnique
  return $ Symbol u nullSemantic $ T.pack description


-- | A list in Edh is a multable, singly-linked, prepend list.
data List = List !Unique !(TVar [EdhValue])
instance Eq List where
  List x'u _ == List y'u _ = x'u == y'u
instance Ord List where
  compare (List x'u _) (List y'u _) = compare x'u y'u
instance Hashable List where
  hashWithSalt s (List u _) = hashWithSalt s u
instance Show List where
  show (List _ !l) = if null ll
    then "[]"
    else "[ " ++ concat [ show i ++ ", " | i <- ll ] ++ "]"
    where ll = unsafePerformIO $ readTVarIO l


-- | The execution context of an Edh thread
data Context = Context {
    -- | the Edh world in context
    contextWorld :: !EdhWorld
    -- | the call stack frames of Edh procedures
    , callStack :: !(NonEmpty Scope)
    -- | the direct generator caller
    , generatorCaller :: !(Maybe EdhGenrCaller)
    -- | the match target value in context, normally be `true`, or the
    -- value from `x` in a `case x of` block
    , contextMatch :: EdhValue
    -- | currently executing statement
    , contextStmt :: !StmtSrc
  }
contextScope :: Context -> Scope
contextScope = NE.head . callStack

type EdhGenrCaller
  = (EdhProgState, EdhValue -> (EdhValue -> STM ()) -> EdhProg (STM ()))


-- | An Edh value with the origin where it came from
data OriginalValue = OriginalValue {
    valueFromOrigin :: !EdhValue
    -- | the scope from which this value is addressed off
    , originScope :: !Scope
    -- | the attribute resolution target object in obtaining this value
    , originObject :: !Object
  }


-- Especially note that Edh has no block scope as in C
-- family languages, JavaScript neither does before ES6,
-- Python neither does until now (2020).
--
-- There is only `procedure scope` in Edh
-- also see https://github.com/e-wrks/edh/Tour/#procedure
--
-- Every non-host procedure call will create a new scope, with a new
-- entity created for it, that:
--
--  * if it is a constructor procedure call, a new object of the called
--    class, or the `<module>` class defined by the world, is allocated
--    viewing the entity, serving `this` object of the scope;
--
--  * if it is a methd procedure call, no new object is created, and the
--    scope inherits `this` object from the lexical outer scope, and the
--    original object from which the method was obtained, becomes `that`
--    object in this scope. `that` either contains the method in its 
--    entity as an attribute, or inherits the method from one of its
--    supers.
--
data Scope = Scope {
    -- | the entity of this scope, it's unique in a method procedure,
    -- and is the underlying entity of 'thisObject' in a class procedure.
    scopeEntity :: !Entity
    -- | `this` object in this scope
    , thisObject :: !Object
    -- | `that` object in this scope
    -- `that` is the same as `this` unless in a scope of super-method call
    , thatObject :: !Object
    -- | the Edh procedure holding this scope
    , scopeProc :: !ProcDefi
  }
instance Eq Scope where
  Scope x'e _ _ _ == Scope y'e _ _ _ = x'e == y'e
instance Ord Scope where
  compare (Scope x'u _ _ _) (Scope y'u _ _ _) = compare x'u y'u
instance Hashable Scope where
  hashWithSalt s (Scope u _ _ _) = hashWithSalt s u
instance Show Scope where
  show (Scope _ _ _ (ProcDefi _ (ProcDecl _ pName argsRcvr (StmtSrc (!srcPos, _)))))
    = "<"
      ++ T.unpack pName
      ++ " "
      ++ show argsRcvr
      ++ " @ "
      ++ sourcePosPretty srcPos
      ++ ">"

outerScopeOf :: Scope -> Maybe Scope
outerScopeOf = procedure'lexi . scopeProc

objectScope :: Object -> Scope
objectScope obj = Scope { scopeEntity = objEntity obj
                        , thisObject  = obj
                        , thatObject  = obj
                        , scopeProc   = objClass obj
                        }

-- | An object views an entity, with inheritance relationship 
-- to any number of super objects.
data Object = Object {
    -- | the entity stores attribute set of the object
      objEntity :: !Entity
    -- | the class (a.k.a constructor) procedure of the object
    , objClass :: !ProcDefi
    -- | up-links for object inheritance hierarchy
    , objSupers :: !(TVar [Object])
  }
instance Eq Object where
  Object x'u _ _ == Object y'u _ _ = x'u == y'u
instance Ord Object where
  compare (Object x'u _ _) (Object y'u _ _) = compare x'u y'u
instance Hashable Object where
  hashWithSalt s (Object u _ _) = hashWithSalt s u
instance Show Object where
  -- it's not right to call 'atomically' here to read 'objSupers' for
  -- the show, as 'show' may be called from an stm transaction, stm
  -- will fail hard on encountering of nested 'atomically' calls.
  show (Object _ (ProcDefi _ (ProcDecl _ cn _ _)) _) =
    "<object: " ++ T.unpack cn ++ ">"

-- | View an entity as object of specified class with specified ancestors
-- this is the black magic you want to avoid
viewAsEdhObject :: Entity -> Class -> [Object] -> STM Object
viewAsEdhObject ent cls supers = Object ent cls <$> newTVar supers


-- | A world for Edh programs to change
data EdhWorld = EdhWorld {
    -- | root scope of this world
    worldScope :: !Scope
    -- | all scope wrapper objects in this world belong to the same
    -- class as 'scopeSuper' and have it as the top most super,
    -- the bottom super of a scope wraper object is the original
    -- `this` object of that scope, thus an attr addressor can be
    -- used to read the attribute value out of the wrapped scope, when
    -- the attr name does not conflict with scope wrapper methods
    , scopeSuper :: !Object
    -- | all operators declared in this world, this also used as the
    -- _world lock_ in parsing source code to be executed in this world
    , worldOperators :: !(TMVar OpPrecDict)
    -- | all modules loaded or being loaded into this world, for each
    -- entry, will be a transient entry containing an error value if
    -- failed loading, or a permanent entry containing the module object
    -- if successfully loaded
    , worldModules :: !(TMVar (Map.HashMap ModuleId (TMVar EdhValue)))
    -- | interface to the embedding host runtime
    , worldRuntime :: !(TMVar EdhRuntime)
  }
instance Eq EdhWorld where
  EdhWorld x'root _ _ _ _ == EdhWorld y'root _ _ _ _ = x'root == y'root

type ModuleId = Text

worldContext :: EdhWorld -> Context
worldContext !world = Context { contextWorld    = world
                              , callStack       = worldScope world :| []
                              , generatorCaller = Nothing
                              , contextMatch    = true
                              , contextStmt     = voidStatement
                              }
{-# INLINE worldContext #-}

data EdhRuntime = EdhRuntime {
  runtimeLogger :: !EdhLogger
  , runtimeLogLevel :: !LogLevel
  }
type EdhLogger = LogLevel -> Maybe String -> ArgsPack -> STM ()
type LogLevel = Int


voidStatement :: StmtSrc
voidStatement = StmtSrc
  ( SourcePos { sourceName   = "<genesis>"
              , sourceLine   = mkPos 1
              , sourceColumn = mkPos 1
              }
  , VoidStmt
  )
{-# INLINE voidStatement #-}

-- | The ultimate nothingness (Chinese 无极/無極), i.e. <nothing> out of <chaos>
wuji :: EdhProgState -> OriginalValue
wuji !pgs = OriginalValue nil rootScope $ thisObject rootScope
  where rootScope = worldScope $ contextWorld $ edh'context pgs
{-# INLINE wuji #-}


-- | The monad for running of an Edh program
type EdhProg = ReaderT EdhProgState STM

-- | The states of a program
data EdhProgState = EdhProgState {
    edh'fork'queue :: !(TQueue (Either (IO ()) EdhTxTask))
    , edh'task'queue :: !(TQueue EdhTxTask)
    , edh'reactors :: !(TVar [ReactorRecord])
    , edh'defers :: !(TVar [DeferRecord])
    , edh'in'tx :: !Bool
    , edh'context :: !Context
  }

type ReactorRecord = (TChan EdhValue, EdhProgState, ArgsReceiver, StmtSrc)
type DeferRecord = (EdhProgState, EdhProg (STM ()))

-- | Run an Edh program from within STM monad
runEdhProg :: EdhProgState -> EdhProg (STM ()) -> STM ()
runEdhProg !pgs !prog = join $ runReaderT prog pgs
{-# INLINE runEdhProg #-}

forkEdh :: EdhProcExit -> EdhProg (STM ()) -> EdhProg (STM ())
forkEdh !exit !prog = ask >>= \pgs -> if edh'in'tx pgs
  then throwEdh EvalError "You don't fork within a transaction"
  else contEdhSTM $ do
    writeTQueue (edh'fork'queue pgs) $ Right $ EdhTxTask pgs
                                                         False
                                                         (wuji pgs)
                                                         (const prog)
    exitEdhSTM pgs exit nil

-- | Continue an Edh program with stm computation, there must be NO further
-- action following this statement, or the stm computation is just lost.
--
-- Note: this is just `return`, but procedures writen in the host language
-- (i.e. Haskell) with this instead of `return` will be more readable.
contEdhSTM :: STM () -> EdhProg (STM ())
contEdhSTM = return
{-# INLINE contEdhSTM #-}

-- | Convenient function to be used as short-hand to return from an Edh
-- procedure (or functions with similar signature), this sets transaction
-- boundaries wrt tx stated in the program's current state.
exitEdhProc :: EdhProcExit -> EdhValue -> EdhProg (STM ())
exitEdhProc !exit !val = ask >>= \pgs -> contEdhSTM $ exitEdhSTM pgs exit val
{-# INLINE exitEdhProc #-}
exitEdhProc' :: EdhProcExit -> OriginalValue -> EdhProg (STM ())
exitEdhProc' !exit !result =
  ask >>= \pgs -> contEdhSTM $ exitEdhSTM' pgs exit result
{-# INLINE exitEdhProc' #-}

-- | Exit an stm computation to the specified Edh continuation
exitEdhSTM :: EdhProgState -> EdhProcExit -> EdhValue -> STM ()
exitEdhSTM !pgs !exit !val =
  let !scope  = contextScope $ edh'context pgs
      !result = OriginalValue { valueFromOrigin = val
                              , originScope     = scope
                              , originObject    = thatObject scope
                              }
  in  exitEdhSTM' pgs exit result
{-# INLINE exitEdhSTM #-}
exitEdhSTM' :: EdhProgState -> EdhProcExit -> OriginalValue -> STM ()
exitEdhSTM' !pgs !exit !result = if edh'in'tx pgs
  then join $ runReaderT (exit result) pgs
  else writeTQueue (edh'task'queue pgs) $ EdhTxTask pgs False result exit
{-# INLINE exitEdhSTM' #-}

-- | An atomic task, an Edh program is composed of many this kind of tasks.
data EdhTxTask = EdhTxTask {
    edh'task'pgs :: !EdhProgState
    , edh'task'wait :: !Bool
    , edh'task'input :: !OriginalValue
    , edh'task'job :: !(OriginalValue -> EdhProg (STM ()))
  }

-- | Instruct the Edh program driver to not auto retry the specified stm
-- action, i.e. let stm retry it automatically (e.g. to blocking read a 'TChan')
waitEdhSTM :: EdhProgState -> STM EdhValue -> (EdhValue -> STM ()) -> STM ()
waitEdhSTM !pgs !act !exit = if edh'in'tx pgs
  then throwEdhSTM pgs EvalError "You don't wait stm from within a transaction"
  else writeTQueue
    (edh'task'queue pgs)
    EdhTxTask
      { edh'task'pgs   = pgs
      , edh'task'wait  = True
      , edh'task'input = wuji pgs
      , edh'task'job   = \_ -> contEdhSTM $ act >>= \val -> writeTQueue
                           (edh'task'queue pgs)
                           EdhTxTask { edh'task'pgs   = pgs
                                     , edh'task'wait  = False
                                     , edh'task'input = wuji pgs
                                     , edh'task'job = \_ -> contEdhSTM $ exit val
                                     }
      }

-- | Blocking wait an asynchronous IO action from current Edh thread
edhWaitIO :: EdhProcExit -> IO EdhValue -> EdhProg (STM ())
edhWaitIO !exit !act = ask >>= \pgs -> if edh'in'tx pgs
  then throwEdh EvalError "You don't wait IO within a transaction"
  else contEdhSTM $ do
    !ioResult <- newEmptyTMVar
    writeTQueue (edh'fork'queue pgs)
      $ Left
      $ catch (act >>= atomically . void . tryPutTMVar ioResult . Right)
      $ \(e :: SomeException) -> atomically $ putTMVar ioResult (Left e)
    writeTQueue (edh'task'queue pgs) $ EdhTxTask pgs True (wuji pgs) $ \_ ->
      contEdhSTM $ readTMVar ioResult >>= \case
        Right v -> exitEdhSTM pgs exit v
        Left  e -> throwEdhSTM pgs EvalError $ T.pack $ displayException e

-- | Type of a procedure in host language that can be called from Edh code.
--
-- Note the caller context/scope can be obtained from callstack of the
-- program state.
type EdhProcedure -- such a procedure servs as the callee
  =  ArgsSender  -- ^ the manifestation of how the caller wills to send args
  -> EdhProcExit -- ^ the CPS exit to return a value from this procedure
  -> EdhProg (STM ())

-- | The type for an Edh procedure's return, in continuation passing style.
type EdhProcExit = OriginalValue -> EdhProg (STM ())

-- | A CPS nop as an Edh procedure exit
edhNop :: EdhProcExit
edhNop _ = return $ return ()

-- | Construct an error context from program state and specified message
getEdhErrorContext :: EdhProgState -> Text -> EdhErrorContext
getEdhErrorContext !pgs !msg =
  let
    !ctx               = edh'context pgs
    (StmtSrc (!sp, _)) = contextStmt ctx
    !frames =
      foldl'
          (\sfs (Scope _ _ _ (ProcDefi _ (ProcDecl _ procName _ (StmtSrc (spos, _))))) ->
            (procName, T.pack (sourcePosPretty spos)) : sfs
          )
          []
        $ NE.init (callStack ctx)
  in
    EdhErrorContext msg (T.pack $ sourcePosPretty sp) frames

-- | Throw from an Edh program, be cautious NOT to have any monadic action
-- following such a throw, or it'll silently fail to work out.
throwEdh :: Exception e => (EdhErrorContext -> e) -> Text -> EdhProg (STM ())
throwEdh !excCtor !msg = do
  !pgs <- ask
  return $ throwSTM (excCtor $ getEdhErrorContext pgs msg)

-- | Throw from the stm operation of an Edh program.
throwEdhSTM
  :: Exception e => EdhProgState -> (EdhErrorContext -> e) -> Text -> STM a
throwEdhSTM pgs !excCtor !msg = throwSTM (excCtor $ getEdhErrorContext pgs msg)


-- | A pack of evaluated argument values with positional/keyword origin,
-- normally obtained by invoking `packEdhArgs ctx argsSender`.
data ArgsPack = ArgsPack {
    positional'args :: ![EdhValue]
    , keyword'args :: !(Map.HashMap AttrName EdhValue)
  } deriving (Eq)
instance Hashable ArgsPack where
  hashWithSalt s (ArgsPack args kwargs) =
    foldl' (\s' (k, v) -> s' `hashWithSalt` k `hashWithSalt` v)
           (foldl' hashWithSalt s args)
      $ Map.toList kwargs
instance Show ArgsPack where
  show (ArgsPack posArgs kwArgs) = if null posArgs && Map.null kwArgs
    then "()"
    else
      "( "
      ++ concat [ show i ++ ", " | i <- posArgs ]
      ++ concat
           [ T.unpack kw ++ "=" ++ show v ++ ", "
           | (kw, v) <- Map.toList kwArgs
           ]
      ++ ")"


-- | Type of procedures implemented in the host language (Haskell).
data HostProcedure = HostProcedure {
    hostProc'uniq :: !Unique
    , hostProc'name :: !Text
    , hostProc'proc :: !EdhProcedure
  }
instance Eq HostProcedure where
  HostProcedure x'u _ _ == HostProcedure y'u _ _ = x'u == y'u
instance Ord HostProcedure where
  compare (HostProcedure x'u _ _) (HostProcedure y'u _ _) = compare x'u y'u
instance Hashable HostProcedure where
  hashWithSalt s (HostProcedure u _ _) = hashWithSalt s u
instance Show HostProcedure where
  show (HostProcedure _ pn _) = "<hostproc: " <> T.unpack pn <> ">"

hostProcDefi :: HostProcedure -> STM ProcDefi
hostProcDefi !hp = do
  u <- unsafeIOToSTM newUnique
  return ProcDefi
    { procedure'lexi = Nothing
    , procedure'decl = ProcDecl
                         { procedure'uniq = u
                         , procedure'name = hostProc'name hp
                         , procedure'args = WildReceiver
                         , procedure'body = StmtSrc
                                              ( SourcePos
                                                { sourceName   = "<hostcode>"
                                                , sourceLine   = mkPos 1
                                                , sourceColumn = mkPos 1
                                                }
                                              , VoidStmt
                                              )
                         }
    }

-- | An event sink is similar to a Go channel, but is broadcast
-- in nature, in contrast to the unicast nature of channels in Go.
data EventSink = EventSink {
    evs'uniq :: !Unique
    -- | sequence number, increased on every new event posting.
    -- must read zero when no event has ever been posted to this sink,
    -- non-zero otherwise. monotonicly increasing most of the time,
    -- but allowed to wrap back to 1 when exceeded 'maxBound::Int'
    -- negative values can be used to indicate abnormal conditions.
    , evs'seqn :: !(TVar Int)
    -- | most recent value, not valid until evs'seqn turns non-zero
    , evs'mrv :: !(TVar EdhValue)
    -- | the broadcast channel
    , evs'chan :: !(TChan EdhValue)
    -- | subscriber counter
    , evs'subc :: !(TVar Int)
  }
instance Eq EventSink where
  EventSink x'u _ _ _ _ == EventSink y'u _ _ _ _ = x'u == y'u
instance Ord EventSink where
  compare (EventSink x'u _ _ _ _) (EventSink y'u _ _ _ _) = compare x'u y'u
instance Hashable EventSink where
  hashWithSalt s (EventSink s'u _ _ _ _) = hashWithSalt s s'u
instance Show EventSink where
  show EventSink{} = "<sink>"


-- Atop Haskell, most types in Edh the surface language, are for
-- immutable values, besides dict and list, the only other mutable
-- data structure in Edh, is the entity, an **entity** is a set of
-- mutable attributes.
--
-- After applied a set of rules/constraints about how attributes
-- of an entity can be retrived and altered, it becomes an object.
--
-- Theoretically an entity is not necessarily mandated to have an
-- `identity` attribute among others, while practically the memory
-- address for physical storage of the attribute set, naturally
-- serves an `identity` attribute in single-process + single-run
-- scenario. Distributed programs, especially using a separate
-- database for storage, will tend to define a generated UUID 
-- attribute or the like.

-- | everything in Edh is a value
data EdhValue =
  -- | type itself is a kind of (immutable) value
      EdhType !EdhTypeValue
  -- | end values (immutable)
    | EdhNil
    | EdhDecimal !Decimal
    | EdhBool !Bool
    | EdhString !Text
    | EdhSymbol !Symbol

  -- | direct pointer (to entities) values
    | EdhObject !Object

  -- | mutable containers
    | EdhDict !Dict
    | EdhList !List

  -- | immutable containers
  --   the elements may still pointer to mutable data
    | EdhPair !EdhValue !EdhValue
    | EdhTuple ![EdhValue]
    | EdhArgsPack ArgsPack

  -- | host procedures callable from Edh world
    | EdhHostProc !HostProcedure
    | EdhHostOper !Precedence !HostProcedure
    | EdhHostGenr !HostProcedure

  -- | precedures defined by Edh code
    | EdhClass !ProcDefi
    | EdhMethod !ProcDefi
    | EdhOperator !Precedence !(Maybe EdhValue) !ProcDefi
    | EdhGenrDef !ProcDefi
    | EdhInterpreter !ProcDefi
    | EdhProducer !ProcDefi

  -- | flow control
    | EdhBreak
    | EdhContinue
    | EdhCaseClose !EdhValue
    | EdhFallthrough
    | EdhYield !EdhValue
    | EdhReturn !EdhValue

  -- | event sink
    | EdhSink !EventSink

  -- | reflection
    | EdhExpr !Unique !Expr

edhValueStr :: EdhValue -> Text
edhValueStr (EdhString s) = s
edhValueStr v             = T.pack $ show v

edhValueNull :: EdhValue -> STM Bool
edhValueNull EdhNil                       = return True
edhValueNull (EdhDecimal d              ) = return $ D.decimalIsNaN d || d == 0
edhValueNull (EdhBool    b              ) = return b
edhValueNull (EdhString  s              ) = return $ T.null s
edhValueNull (EdhSymbol  (Symbol _ ns _)) = return ns
edhValueNull (EdhDict    (Dict _ d     )) = Map.null <$> readTVar d
edhValueNull (EdhList    (List _ l     )) = null <$> readTVar l
edhValueNull (EdhTuple   l              ) = return $ null l
edhValueNull (EdhArgsPack (ArgsPack args kwargs)) =
  return $ null args && Map.null kwargs
edhValueNull _ = return False

instance Show EdhValue where
  show (EdhType t)    = show t
  show EdhNil         = "nil"
  show (EdhDecimal v) = showDecimal v
  show (EdhBool    v) = if v then "true" else "false"
  show (EdhString  v) = show v
  show (EdhSymbol  v) = show v

  show (EdhObject  v) = show v

  show (EdhDict    v) = show v
  show (EdhList    v) = show v

  show (EdhPair k v ) = show k <> ":" <> show v
  show (EdhTuple v  ) = if null v
    then "(,)" -- mimic the denotation of empty tuple in Python
    else -- advocate trailing comma here
         "( " ++ concat [ show i ++ ", " | i <- v ] ++ ")"
  show (EdhArgsPack v) = "pkargs" ++ show v

  show (EdhHostProc v) = show v
  show (EdhHostOper prec (HostProcedure _ pn _)) =
    "<hostop: (" <> T.unpack pn <> ") " <> show prec <> ">"
  show (EdhHostGenr (HostProcedure _ pn _)) =
    "<hostgen: " <> T.unpack pn <> ">"

  show (EdhClass (ProcDefi _ (ProcDecl _ pn _ _))) =
    "<class: " ++ T.unpack pn ++ ">"
  show (EdhMethod (ProcDefi _ (ProcDecl _ pn _ _))) =
    "<method: " ++ T.unpack pn ++ ">"
  show (EdhOperator precedence _predecessor (ProcDefi _ (ProcDecl _ pn _ _))) =
    "<operator: (" ++ T.unpack pn ++ ") " ++ show precedence ++ ">"
  show (EdhGenrDef (ProcDefi _ (ProcDecl _ pn _ _))) =
    "<generator: " ++ T.unpack pn ++ ">"
  show (EdhInterpreter (ProcDefi _ (ProcDecl _ pn _ _))) =
    "<interpreter: " ++ T.unpack pn ++ ">"
  show (EdhProducer (ProcDefi _ (ProcDecl _ pn _ _))) =
    "<producer: " ++ T.unpack pn ++ ">"

  show EdhBreak         = "<break>"
  show EdhContinue      = "<continue>"
  show (EdhCaseClose v) = "<caseclose: " ++ show v ++ ">"
  show EdhFallthrough   = "<fallthrough>"
  show (EdhYield  v)    = "<yield: " ++ show v ++ ">"
  show (EdhReturn v)    = "<return: " ++ show v ++ ">"

  show (EdhSink   v)    = show v

  show (EdhExpr _ v)    = "<expr: " ++ show v ++ ">"

-- Note:
--
-- here is identity-wise equality i.e. pointer equality if mutable,
-- or value equality if immutable.
--
-- the semantics are different from value-wise equality especially
-- for types of:  object/dict/list

instance Eq EdhValue where
  EdhType x            == EdhType y            = x == y
  EdhNil               == EdhNil               = True
  EdhDecimal x         == EdhDecimal y         = x == y
  EdhBool    x         == EdhBool    y         = x == y
  EdhString  x         == EdhString  y         = x == y
  EdhSymbol  x         == EdhSymbol  y         = x == y

  EdhObject  x         == EdhObject  y         = x == y

  EdhDict    x         == EdhDict    y         = x == y
  EdhList    x         == EdhList    y         = x == y
  EdhPair x'k x'v      == EdhPair y'k y'v      = x'k == y'k && x'v == y'v
  EdhTuple    x        == EdhTuple    y        = x == y
  EdhArgsPack x        == EdhArgsPack y        = x == y

  EdhHostProc x        == EdhHostProc y        = x == y
  EdhHostOper _ x'proc == EdhHostOper _ y'proc = x'proc == y'proc
  EdhHostGenr x        == EdhHostGenr y        = x == y

  EdhClass    x        == EdhClass    y        = x == y
  EdhMethod   x        == EdhMethod   y        = x == y
  EdhOperator _ _ x    == EdhOperator _ _ y    = x == y
  EdhGenrDef     x     == EdhGenrDef     y     = x == y
  EdhInterpreter x     == EdhInterpreter y     = x == y
  EdhProducer    x     == EdhProducer    y     = x == y

  EdhBreak             == EdhBreak             = True
  EdhContinue          == EdhContinue          = True
  EdhCaseClose x       == EdhCaseClose y       = x == y
  EdhFallthrough       == EdhFallthrough       = True
-- todo: regard a yielded/returned value equal to the value itself ?
  EdhYield  x'v        == EdhYield  y'v        = x'v == y'v
  EdhReturn x'v        == EdhReturn y'v        = x'v == y'v

  EdhSink   x          == EdhSink   y          = x == y

  EdhExpr x'u _        == EdhExpr y'u _        = x'u == y'u

-- todo: support coercing equality ?
--       * without this, we are a strongly typed dynamic language
--       * with this, we'll be a weakly typed dynamic language
  _                    == _                    = False

instance Hashable EdhValue where
  hashWithSalt s (EdhType x)         = hashWithSalt s $ 1 + fromEnum x
  hashWithSalt s EdhNil              = hashWithSalt s (0 :: Int)
  hashWithSalt s (EdhDecimal x     ) = hashWithSalt s x
  hashWithSalt s (EdhBool    x     ) = hashWithSalt s x
  hashWithSalt s (EdhString  x     ) = hashWithSalt s x
  hashWithSalt s (EdhSymbol  x     ) = hashWithSalt s x
  hashWithSalt s (EdhObject  x     ) = hashWithSalt s x

  hashWithSalt s (EdhDict    x     ) = hashWithSalt s x
  hashWithSalt s (EdhList    x     ) = hashWithSalt s x
  hashWithSalt s (EdhPair k v      ) = s `hashWithSalt` k `hashWithSalt` v
  hashWithSalt s (EdhTuple    x    ) = foldl' hashWithSalt s x
  hashWithSalt s (EdhArgsPack x    ) = hashWithSalt s x

  hashWithSalt s (EdhHostProc x    ) = hashWithSalt s x
  hashWithSalt s (EdhHostOper _ x  ) = hashWithSalt s x
  hashWithSalt s (EdhHostGenr x    ) = hashWithSalt s x

  hashWithSalt s (EdhClass    x    ) = hashWithSalt s x
  hashWithSalt s (EdhMethod   x    ) = hashWithSalt s x
  hashWithSalt s (EdhOperator _ _ x) = hashWithSalt s x
  hashWithSalt s (EdhGenrDef     x ) = hashWithSalt s x
  hashWithSalt s (EdhInterpreter x ) = hashWithSalt s x
  hashWithSalt s (EdhProducer    x ) = hashWithSalt s x

  hashWithSalt s EdhBreak            = hashWithSalt s (-1 :: Int)
  hashWithSalt s EdhContinue         = hashWithSalt s (-2 :: Int)
  hashWithSalt s (EdhCaseClose v) =
    s `hashWithSalt` (-3 :: Int) `hashWithSalt` v
  hashWithSalt s EdhFallthrough = hashWithSalt s (-4 :: Int)
  hashWithSalt s (EdhYield  v)  = s `hashWithSalt` (-5 :: Int) `hashWithSalt` v
  hashWithSalt s (EdhReturn v)  = s `hashWithSalt` (-6 :: Int) `hashWithSalt` v

  hashWithSalt s (EdhSink   x)  = hashWithSalt s x

  hashWithSalt s (EdhExpr u _)  = hashWithSalt s u


nil :: EdhValue
nil = EdhNil

nan :: EdhValue
nan = EdhDecimal D.nan

inf :: EdhValue
inf = EdhDecimal D.inf

true :: EdhValue
true = EdhBool True

false :: EdhValue
false = EdhBool False


newtype StmtSrc = StmtSrc (SourcePos, Stmt)
instance Eq StmtSrc where
  StmtSrc (x'sp, x'stmt) == StmtSrc (y'sp, y'stmt) =
    x'sp == y'sp && x'stmt == y'stmt
instance Show StmtSrc where
  show (StmtSrc (sp, stmt)) = show stmt ++ "\n@ " ++ sourcePosPretty sp


data Stmt =
      -- | literal `pass` to fill a place where a statement needed,
      -- same as in Python
      VoidStmt
      -- | atomically isolated, mark a code section for transaction bounds
    | AtoIsoStmt !Expr
      -- | similar to `go` in Go, starts goroutine
    | GoStmt !Expr
      -- | not similar to `defer` in Go (in Go `defer` snapshots arg values
      -- and schedules execution on func return), but in Edh `defer`
      -- schedules execution on thread termination
    | DeferStmt !Expr
      -- | import with args (re)pack receiving syntax
    | ImportStmt !ArgsReceiver !Expr
      -- | assignment with args (un/re)pack sending/receiving syntax
    | LetStmt !ArgsReceiver !ArgsSender
      -- | super object declaration for a descendant object
    | ExtendsStmt !Expr
      -- | class (constructor) procedure definition
    | ClassStmt !ProcDecl
      -- | method procedure definition
    | MethodStmt !ProcDecl
      -- | generator procedure definition
    | GeneratorStmt !ProcDecl
      -- | reactor declaration, a reactor procedure is not bound to a name,
      -- it's bound to an event `sink` with the calling thread as context,
      -- when an event fires from that event `sink`, the bound reactor will
      -- get run from the thread where it's declared, after the currernt
      -- transaction finishes, a reactor procedure can `break` to terminate
      -- the thread, or the thread will continue to process next reactor, or
      -- next transactional task normally
      -- the reactor mechanism is somewhat similar to traditional signal
      -- handling mechanism in OS process management
    | ReactorStmt !Expr !ArgsReceiver !StmtSrc
      -- | interpreter declaration, an interpreter procedure is not otherwise
      -- different from a method procedure, except it receives arguments
      -- in expression form rather than values, in addition to the reflective
      -- `callerScope` as first argument
    | InterpreterStmt !ProcDecl
    | ProducerStmt !ProcDecl
      -- | while loop
    | WhileStmt !Expr !StmtSrc
      -- | break from a while/for loop, or terminate the Edh thread if given
      -- from a reactor
    | BreakStmt
      -- | continue a while/for loop
    | ContinueStmt
      -- | similar to fallthrough in Go
    | FallthroughStmt
      -- | operator declaration
    | OpDeclStmt !OpSymbol !Precedence !ProcDecl
      -- | operator override
    | OpOvrdStmt !OpSymbol !ProcDecl !Precedence
      -- | similar to exception mechanism in JavaScript
    | ThrowStmt !Expr | TryStmt {
        try'trunk :: !StmtSrc
        , try'catches :: ![(Expr, Maybe AttrName, StmtSrc)]
        , try'finally :: !(Maybe StmtSrc)
        }
      -- | early stop from a procedure
    | ReturnStmt !Expr
      -- | expression with precedence
    | ExprStmt !Expr
  deriving (Eq, Show)

-- Attribute addressor
data AttrAddr = ThisRef | ThatRef | SuperRef
    | DirectRef !AttrAddressor
    | IndirectRef !Expr !AttrAddressor
  deriving (Eq, Show)

data AttrAddressor =
    -- | vanilla form in addressing attributes against
    --   a left hand entity object
    NamedAttr !AttrName
    -- | get the symbol value from current entity,
    --   then use it to address attributes against
    --   a left hand entity object
    | SymbolicAttr !AttrName
  deriving (Eq, Show)


receivesNamedArg :: Text -> ArgsReceiver -> Bool
receivesNamedArg _     WildReceiver              = True
receivesNamedArg !name (SingleReceiver argRcvr ) = _hasNamedArg name [argRcvr]
receivesNamedArg !name (PackReceiver   argRcvrs) = _hasNamedArg name argRcvrs

_hasNamedArg :: Text -> [ArgReceiver] -> Bool
_hasNamedArg _     []           = False
_hasNamedArg !name (arg : rest) = case arg of
  RecvArg !argName _ _ -> argName == name || _hasNamedArg name rest
  _                    -> _hasNamedArg name rest

data ArgsReceiver = PackReceiver ![ArgReceiver]
    | SingleReceiver !ArgReceiver
    | WildReceiver
  deriving (Eq)
instance Show ArgsReceiver where
  show (PackReceiver   rs) = "( " ++ unwords ((++ ", ") . show <$> rs) ++ ")"
  show (SingleReceiver r ) = "(" ++ show r ++ ")"
  show WildReceiver        = "*"

data ArgReceiver = RecvRestPosArgs !AttrName
    | RecvRestKwArgs !AttrName
    | RecvRestPkArgs !AttrName
    | RecvArg !AttrName !(Maybe AttrAddr) !(Maybe Expr)
  deriving (Eq)
instance Show ArgReceiver where
  show (RecvRestPosArgs nm) = "*" ++ T.unpack nm
  show (RecvRestKwArgs  nm) = "**" ++ T.unpack nm
  show (RecvRestPkArgs  nm) = "***" ++ T.unpack nm
  show (RecvArg nm _ _    ) = T.unpack nm

type ArgsSender = [ArgSender]
data ArgSender = UnpackPosArgs !Expr
    | UnpackKwArgs !Expr
    | UnpackPkArgs !Expr
    | SendPosArg !Expr
    | SendKwArg !AttrName !Expr
  deriving (Eq, Show)

-- | Procedure declaration, result of parsing
data ProcDecl = ProcDecl {
      procedure'uniq :: !Unique
    , procedure'name :: !AttrName
    , procedure'args :: !ArgsReceiver
    , procedure'body :: !StmtSrc
  }
instance Eq ProcDecl where
  ProcDecl x'u _ _ _ == ProcDecl y'u _ _ _ = x'u == y'u
instance Ord ProcDecl where
  compare (ProcDecl x'u _ _ _) (ProcDecl y'u _ _ _) = compare x'u y'u
instance Hashable ProcDecl where
  hashWithSalt s (ProcDecl u _ _ _) = hashWithSalt s u
instance Show ProcDecl where
  show (ProcDecl _ name _ _) = "<proc " <> T.unpack name <> ">"

-- | Procedure definition, result of execution of the declaration
data ProcDefi = ProcDefi {
    procedure'lexi :: !(Maybe Scope)
    , procedure'decl :: {-# UNPACK #-} !ProcDecl
  }
instance Eq ProcDefi where
  ProcDefi x's (ProcDecl x'u _ _ _) == ProcDefi y's (ProcDecl y'u _ _ _) =
    x'u == y'u && x's == y's
instance Ord ProcDefi where
  compare (ProcDefi x's (ProcDecl x'u _ _ _)) (ProcDefi y's (ProcDecl y'u _ _ _))
    = case declResult of
      EQ -> compare x's y's
      _  -> declResult
    where !declResult = compare x'u y'u
instance Hashable ProcDefi where
  hashWithSalt s (ProcDefi scope (ProcDecl u _ _ _)) =
    s `hashWithSalt` u `hashWithSalt` scope

lexicalScopeOf :: ProcDefi -> Scope
lexicalScopeOf (ProcDefi (Just scope) _) = scope
lexicalScopeOf (ProcDefi Nothing _) =
  error "bug: asking for scope of world root"

-- | The class is a special type of procedure, receives no argument.
type Class = ProcDefi


data Prefix = PrefixPlus | PrefixMinus | Not
    -- | to disregard the match target in context,
    -- for a branch condition
    | Guard
  deriving (Eq, Show)

data Expr = LitExpr !Literal | PrefixExpr !Prefix !Expr
    | IfExpr { if'condition :: !Expr
            , if'consequence :: !StmtSrc
            , if'alternative :: !(Maybe StmtSrc)
            }
    | CaseExpr { case'target :: !Expr , case'branches :: !StmtSrc }

    | DictExpr ![Expr] -- should all be Infix ":"
    | ListExpr ![Expr]
    | TupleExpr ![Expr]
    | ParenExpr !Expr

    -- | the block is made an expression in Edh, instead of a statement
    -- as in a C family language. it evaluates to the value of last expr
    -- within it, in case no `EdhCaseClose` encountered, or can stop
    -- early with the value from a `EdhCaseClose`, typically returned
    -- from the branch `(->)` operator.
    --
    -- this allows multiple statements grouped as a single expression
    -- fitting into subclauses of if-then-else, while, for-from-do,
    -- and try-catch-finally etc. where an expression is expected.
    -- 
    -- this also made possible for a method procedure to explicitly
    -- `return { continue }` to carry a semantic to the magic method
    -- caller that it should try next method, similar to what
    -- `NotImplemented` does in Python.
    | BlockExpr ![StmtSrc]

    | YieldExpr !Expr

    -- | a for-from-do loop is made an expression in Edh, so it can
    -- appear as the right-hand expr of the comprehension (=<) operator.
    | ForExpr !ArgsReceiver !Expr !Expr

    | AttrExpr !AttrAddr
    | IndexExpr { index'value :: !Expr
                , index'target :: !Expr
                }
    | CallExpr !Expr !ArgsSender

    | InfixExpr !OpSymbol !Expr !Expr

    | GodSendExpr EdhValue
  deriving (Eq, Show)


data Literal = NilLiteral
    | DecLiteral !Decimal
    | BoolLiteral !Bool
    | StringLiteral !Text
    | SinkCtor -- sink constructor
    | TypeLiteral !EdhTypeValue
  deriving (Eq, Show)


-- | the type for the value of type of a value
data EdhTypeValue = TypeType
    -- nil has no type, its type if you really ask, is nil
    | DecimalType
    | BoolType
    | StringType
    | SymbolType
    | ObjectType
    | DictType
    | ListType
    | PairType
    | TupleType
    | ArgsPackType
    | BlockType
    | HostProcType
    | HostOperType
    | HostGenrType
    | ClassType
    | MethodType
    | OperatorType
    | GeneratorType
    | InterpreterType
    | ProducerType
    | BreakType
    | ContinueType
    | CaseCloseType
    | FallthroughType
    | YieldType
    | ReturnType
    | SinkType
    | ExprType
  deriving (Enum, Eq, Ord, Show)
instance Hashable EdhTypeValue where
  hashWithSalt s t = hashWithSalt s $ fromEnum t

edhTypeOf :: EdhValue -> EdhValue
edhTypeOf EdhType{}        = EdhType TypeType

edhTypeOf EdhNil           = nil
edhTypeOf EdhDecimal{}     = EdhType DecimalType
edhTypeOf EdhBool{}        = EdhType BoolType
edhTypeOf EdhString{}      = EdhType StringType
edhTypeOf EdhSymbol{}      = EdhType SymbolType
edhTypeOf EdhObject{}      = EdhType ObjectType
edhTypeOf EdhDict{}        = EdhType DictType
edhTypeOf EdhList{}        = EdhType ListType
edhTypeOf EdhPair{}        = EdhType PairType
edhTypeOf EdhTuple{}       = EdhType TupleType
edhTypeOf EdhArgsPack{}    = EdhType ArgsPackType
edhTypeOf EdhHostProc{}    = EdhType HostProcType
edhTypeOf EdhHostOper{}    = EdhType HostOperType
edhTypeOf EdhHostGenr{}    = EdhType HostGenrType
edhTypeOf EdhClass{}       = EdhType ClassType
edhTypeOf EdhMethod{}      = EdhType MethodType
edhTypeOf EdhOperator{}    = EdhType OperatorType
edhTypeOf EdhGenrDef{}     = EdhType GeneratorType
edhTypeOf EdhInterpreter{} = EdhType InterpreterType
edhTypeOf EdhProducer{}    = EdhType ProducerType
edhTypeOf EdhBreak         = EdhType BreakType
edhTypeOf EdhContinue      = EdhType ContinueType
edhTypeOf EdhCaseClose{}   = EdhType CaseCloseType
edhTypeOf EdhFallthrough   = EdhType FallthroughType
edhTypeOf EdhYield{}       = EdhType YieldType
edhTypeOf EdhReturn{}      = EdhType ReturnType
edhTypeOf EdhSink{}        = EdhType SinkType
edhTypeOf EdhExpr{}        = EdhType ExprType
