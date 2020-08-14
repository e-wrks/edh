
module Language.Edh.Details.RtTypes where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )
import           System.IO.Unsafe               ( unsafePerformIO )

import           Control.Monad
import           Control.Concurrent.STM

import           Data.Foldable
import           Data.Unique
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.ByteString                ( ByteString )
import qualified Data.ByteString               as B
import           Data.Hashable
import qualified Data.HashMap.Strict           as Map
import           Data.List.NonEmpty             ( NonEmpty(..)
                                                , (<|)
                                                )
import qualified Data.List.NonEmpty            as NE
import           Data.Dynamic

import qualified Data.UUID                     as UUID
import qualified Data.UUID.V4                  as UUID

import           Text.Megaparsec

import           Data.Lossless.Decimal         as D

import           Language.Edh.Control

import           Language.Edh.Details.IOPD



-- TODO rm this after refactor done
lexicalScopeOf :: ProcDefi -> Scope
lexicalScopeOf = edh'procedure'lexi



-- | A pack of evaluated argument values with positional/keyword origin,
-- this works in places of tuples in other languages, apk in Edh can be
-- considered a tuple if only positional arguments inside.
-- Specifically, an empty apk is just considered an empty tuple.
data ArgsPack = ArgsPack {
    positional'args :: ![EdhValue]
    , keyword'args :: !(OrderedDict AttrKey EdhValue)
  } deriving (Eq)
instance Hashable ArgsPack where
  hashWithSalt s (ArgsPack !args !kwargs) =
    s `hashWithSalt` args `hashWithSalt` kwargs
instance Show ArgsPack where
  show (ArgsPack !args kwargs) = if null args && odNull kwargs
    then "()"
    else
      "( "
      ++ concat [ show p ++ ", " | p <- args ]
      ++ concat
           [ show kw ++ "=" ++ show v ++ ", " | (kw, v) <- odToList kwargs ]
      ++ ")"


-- | A dict in Edh is neither an object nor an entity, but just a
-- mutable associative array.
data Dict = Dict !Unique !DictStore
instance Eq Dict where
  Dict x'u _ == Dict y'u _ = x'u == y'u
instance Ord Dict where
  compare (Dict x'u _) (Dict y'u _) = compare x'u y'u
instance Hashable Dict where
  hashWithSalt s (Dict u _) = hashWithSalt s u
instance Show Dict where
  show _ = "<dict>"
type ItemKey = EdhValue
type DictStore = IOPD EdhValue EdhValue

-- | create a new Edh dict from a list of entries
--
-- nil keys and nil values are filtered out so have no effect
createEdhDict :: [(ItemKey, EdhValue)] -> STM Dict
createEdhDict !entries = do
  u <- unsafeIOToSTM newUnique
  Dict u <$> iopdFromList
    [ e | e@(key, val) <- entries, key /= EdhNil && val /= EdhNil ]

-- | setting to `nil` value means deleting the item by the specified key
setDictItem :: ItemKey -> EdhValue -> DictStore -> STM ()
setDictItem !k !v !d = case v of
  EdhNil -> iopdDelete k d
  _      -> iopdInsert k v d

dictEntryList :: DictStore -> STM [EdhValue]
dictEntryList !d =
  (<$> iopdToList d) $ fmap $ \(k, v) -> EdhArgsPack $ ArgsPack [k, v] odEmpty


-- | Backing storage for a scope or a hash object
type EntityStore = IOPD AttrKey EdhValue

data AttrKey = AttrByName !AttrName | AttrBySym !Symbol
    deriving (Eq, Ord)
instance Show AttrKey where
  show (AttrByName attrName      ) = T.unpack attrName
  show (AttrBySym  (Symbol _ sym)) = T.unpack sym
instance Hashable AttrKey where
  hashWithSalt s (AttrByName name) =
    s `hashWithSalt` (0 :: Int) `hashWithSalt` name
  hashWithSalt s (AttrBySym sym) =
    s `hashWithSalt` (1 :: Int) `hashWithSalt` sym

type AttrName = Text

attrKeyValue :: AttrKey -> EdhValue
attrKeyValue (AttrByName nm ) = EdhString nm
attrKeyValue (AttrBySym  sym) = EdhSymbol sym


-- | A symbol can stand in place of an alphanumeric name, used to
-- address an attribute from an object entity, but symbols are 
-- uniquely existing regardless however it is (alphanumerically)
-- named, this can be leveraged to solve naming clashes among
-- modules supplied by different parties.
--
-- And symbol values reside in a lexical outer scope are available
-- to its lexical inner scopes, e.g. a symbol bound to a module is
-- available to all procedures defined in the module, and a symbol
-- bound within a class procedure is available to all its methods
-- as well as nested classes.
data Symbol = Symbol !Unique !Text
instance Eq Symbol where
  Symbol x'u _ == Symbol y'u _ = x'u == y'u
instance Ord Symbol where
  compare (Symbol x'u _) (Symbol y'u _) = compare x'u y'u
instance Hashable Symbol where
  hashWithSalt s (Symbol u _) = hashWithSalt s u
instance Show Symbol where
  show (Symbol _ desc) = T.unpack desc

symbolName :: Symbol -> Text
symbolName (Symbol _ !desc) = case T.stripPrefix "@" desc of
  Nothing    -> desc
  Just !name -> name

globalSymbol :: Text -> Symbol
globalSymbol !description = unsafePerformIO $ do
  !u <- newUnique
  return $ Symbol u description
mkSymbol :: Text -> STM Symbol
mkSymbol !description = do
  !u <- unsafeIOToSTM newUnique
  return $ Symbol u description


mkUUID :: STM UUID.UUID
mkUUID = unsafeIOToSTM UUID.nextRandom


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
    edh'ctx'world :: !EdhWorld
    -- | the call stack frames of Edh procedures
  , edh'ctx'stack :: !(NonEmpty Scope)
    -- | the direct generator caller
  , edh'ctx'genr'caller :: !(Maybe EdhGenrCaller)
    -- | the match target value in context, normally be `true`, or the
    -- value from `x` in a `case x of` block
  , edh'ctx'match :: EdhValue
    -- | currently executing statement
  , edh'ctx'stmt :: !StmtSrc
    -- | whether it's discouraged for procedure definitions or similar
    -- expressions from installing their results as attributes into the
    -- context scope, i.e. the top of current call stack
  , edh'ctx'pure :: !Bool
    -- | whether running within an exporting stmt
  , edh'ctx'exporting :: !Bool
    -- | whether running within an effect stmt
  , edh'ctx'eff'defining :: !Bool
  }
contextScope :: Context -> Scope
contextScope = NE.head . edh'ctx'stack
contextFrame :: Context -> Int -> Scope
contextFrame !ctx !unwind = unwindStack (NE.head stack) (NE.tail stack) unwind
 where
  !stack = edh'ctx'stack ctx
  unwindStack :: Scope -> [Scope] -> Int -> Scope
  unwindStack !s _ !c | c <= 0 = s
  unwindStack !s []         _  = s
  unwindStack _  (s : rest) !c = unwindStack s rest (c - 1)

type EdhGenrCaller
  = ( -- the caller's state
       EdhThreadState
      -- the yield receiver, a.k.a. the caller's continuation
    ,  EdhValue -- one value yielded from the generator
    -> ( -- continuation of the genrator
        -- Left (pgsThrower, exv)
        --   exception to be thrown from that `yield` expr
        -- Right yieldedValue
        --   value given to that `yield` expr
        Either (EdhThreadState, EdhValue) EdhValue -> STM ())
    -> STM ()
    )


type EdhExcptHndlr
  =  EdhValue -- ^ the error value to handle
  -> (EdhValue -> STM ()) -- ^ action to re-throw if not recovered
  -> STM ()

defaultEdhExcptHndlr :: EdhExcptHndlr
defaultEdhExcptHndlr !exv !rethrow = rethrow exv


-- Especially note that Edh has no block scope as in C
-- family languages, JavaScript neither does before ES6,
-- Python neither does until now (3.8).
--
-- There is only `procedure scope` in Edh
-- also see https://github.com/e-wrks/edh/Tour/#procedure
data Scope = Scope {
    -- | the backing storage of this scope, it's unique in a method procedure,
    -- and is the underlying hash store of 'edh'scope'this' in a class procedure.
    edh'scope'entity :: !EntityStore
    -- | `this` object in this scope
  , edh'scope'this :: !Object
    -- | `that` object in this scope
  , edh'scope'that :: !Object
    -- | the exception handler, `catch`/`finally` should capture the
    -- outer scope, and run its *tried* block with a new stack whose
    -- top frame is a scope all same but the `edh'excpt'hndlr` field,
    -- which executes its handling logics appropriately.
  , edh'excpt'hndlr :: !EdhExcptHndlr
    -- | the Edh procedure holding this scope
  , edh'scope'proc :: !ProcDefi
    -- | the Edh stmt caused creation of this scope
  , edh'scope'caller :: !StmtSrc
    -- | when this scope is of an effectful procedure as called, this is the
    -- outer call stack from which (but not including the) scope the
    -- procedure is addressed of
  , edh'effects'stack :: [Scope]
  }
instance Show Scope where
  show (Scope _ _ _ _ (ProcDefi _ _ _ (ProcDecl !addr _ !procBody)) (StmtSrc (!cPos, _)) _)
    = "📜 " ++ show addr ++ " 🔎 " ++ defLoc ++ " 👈 " ++ sourcePosPretty cPos
   where
    defLoc = case procBody of
      Right _                   -> "<host-code>"
      Left  (StmtSrc (dPos, _)) -> sourcePosPretty dPos

outerScopeOf :: Scope -> Maybe Scope
outerScopeOf !scope = if edh'scope'proc outerScope == edh'scope'proc scope
  then Nothing -- already at world root scope
  else Just outerScope
  where !outerScope = edh'procedure'lexi $ edh'scope'proc scope


-- | A class is wrapped as an object per se, the object's storage structure is
-- here:
-- - the procedure created the class, from which the class name, the lexical
--   scope and other information can be obtained
-- - a hash storage of (so called static) attributes shared by all object
--   instances of the class
-- - the storage allocator for new objects of the class to be created
data Class = Class {
    edh'class'proc :: !ProcDefi
  , edh'class'store :: !EntityStore
  , edh'class'allocator :: !EdhObjectAllocator
  }
instance Eq Class where
  Class x'p _ _ == Class y'p _ _ = x'p == y'p
instance Hashable Class where
  hashWithSalt s (Class p _ _) = hashWithSalt s p

type EdhObjectAllocator
  = EdhThreadState -> ArgsPack -> (ObjectStore -> STM ()) -> STM ()


-- | An object views an entity, with inheritance relationship 
-- to any number of super objects.
data Object = Object {
    -- | unique identifier of an Edh object
    edh'obj'ident :: !Unique
    -- | the storage for entity attributes of the object
  , edh'obj'store :: !ObjectStore
    -- | the class object must have a 'ClassStore' storage
  , edh'obj'class :: !Object
    -- | up-links for object inheritance hierarchy
  , edh'obj'supers :: !(TVar [Object])
  }
instance Eq Object where
  Object x'u _ _ _ == Object y'u _ _ _ = x'u == y'u
instance Ord Object where
  compare (Object x'u _ _ _) (Object y'u _ _ _) = compare x'u y'u
instance Hashable Object where
  hashWithSalt s (Object u _ _ _) = hashWithSalt s u
instance Show Object where
  -- it's not right to call 'atomically' here to read 'edh'obj'supers' for
  -- the show, as 'show' may be called from an stm transaction, stm
  -- will fail hard on encountering of nested 'atomically' calls.
  show obj = case edh'obj'store $ edh'obj'class obj of
    ClassStore (Class !pd _ _) ->
      "<object: " ++ T.unpack (procedureName pd) ++ ">"
    _ -> "<bogus-object>"

data ObjectStore =
    HashStore !EntityStore
  | ClassStore !Class -- in case this is a class object
  | HostStore !(TVar Dynamic)

-- | Try cast and unveil an Object's storage of a known type
castObjectStore :: forall a . (Typeable a) => Object -> STM (Maybe a)
castObjectStore !obj = case edh'obj'store obj of
  HostStore !dsv -> fromDynamic <$> readTVar dsv >>= \case
    Just (d :: a) -> return $ Just d
    Nothing       -> return Nothing
  _ -> return Nothing
-- | Try cast and unveil a possible Object's storage of a known type
castObjectStore' :: forall a . (Typeable a) => EdhValue -> STM (Maybe a)
castObjectStore' !val = case edhUltimate val of
  EdhObject !obj -> castObjectStore obj
  _              -> return Nothing


-- | Clone a host data object, with the specified function to clone the
-- 'Dynamic' data store
--
-- CAVEATS:
--  *) all super objects are referenced rather than deep copied
cloneHostObject
  :: Object
  -> (Dynamic -> (Dynamic -> STM ()) -> STM ())
  -> (Object -> STM ())
  -> STM ()
cloneHostObject (Object _ !os !cls !supers) !dsClone !exit = do
  !oid     <- unsafeIOToSTM newUnique
  !supers' <- newTVar =<< readTVar supers
  case os of
    HostStore !dsv -> readTVar dsv >>= \ !ds -> dsClone ds $ \ !ds' -> do
      !dsv' <- newTVar ds'
      exit $ Object oid (HostStore dsv') cls supers'
    _ -> error "not a data object"


edhCreateWorldRoot :: STM Scope
edhCreateWorldRoot = do
  !idMeta <- unsafeIOToSTM newUnique
  !hsMeta <- iopdEmpty
  !ssMeta <- newTVar []

  !idRoot <- unsafeIOToSTM newUnique
  !hsRoot <- iopdEmpty
  !ssRoot <- newTVar []

  let
    metaProc = ProcDefi idMeta (AttrByName "class") rootScope
      $ ProcDecl (NamedAttr "class") (PackReceiver []) (Right edhNop)
    metaClass    = Class metaProc hsMeta metaAllocator
    metaClassObj = Object idMeta (ClassStore metaClass) metaClassObj ssMeta

    rootObj      = Object idRoot (HashStore hsRoot) metaClassObj ssRoot
    rootProc     = ProcDefi idRoot (AttrByName "<root>") rootScope
      $ ProcDecl (NamedAttr "<root>") (PackReceiver []) (Right edhNop)

    rootScope =
      Scope hsRoot rootObj rootObj defaultEdhExcptHndlr rootProc genesisStmt []

  !metaArts <- -- todo more static attrs for class objects here
    sequence
    $  [ (AttrByName nm, ) <$> mkHostProc rootScope EdhMethod nm hp args
       | (nm, hp, args) <- [("__repr__", hpClassRepr, PackReceiver [])]
       ]
    ++ [ (AttrByName nm, ) <$> mkHostProperty rootScope nm getter setter
       | (nm, getter, setter) <- [("name", hpClassNameGetter, Nothing)]
       ]
  iopdUpdate metaArts hsMeta

  return rootScope
 where
  metaAllocator _ _ _ = error "bug: allocating root object"

  hpClassRepr :: EdhProcedure
  hpClassRepr _apk !exit !ets = case edh'obj'store clsObj of
    ClassStore (Class !pd _ _) ->
      exitEdh ets exit $ EdhString $ procedureName pd
    _ -> exitEdh ets exit $ EdhString "<bogus-class>"
    where clsObj = edh'scope'this $ contextScope $ edh'context ets

  hpClassNameGetter :: EdhProcedure
  hpClassNameGetter _apk !exit !ets = case edh'obj'store clsObj of
    ClassStore (Class !pd _ _) ->
      exitEdh ets exit $ attrKeyValue $ edh'procedure'name pd
    _ -> exitEdh ets exit nil
    where clsObj = edh'scope'this $ contextScope $ edh'context ets

  genesisStmt :: StmtSrc
  genesisStmt = StmtSrc
    ( SourcePos { sourceName   = "<genesis>"
                , sourceLine   = mkPos 1
                , sourceColumn = mkPos 1
                }
    , VoidStmt
    )


-- | A world for Edh programs to change
data EdhWorld = EdhWorld {
    -- | root scope of this world
    edh'world'root :: !Scope
    -- | all operators declared in this world, this also used as the
    -- _world lock_ in parsing source code to be executed in this world
  , edh'world'operators :: !(TMVar OpPrecDict)
    -- | all modules loaded or being loaded into this world, for each
    -- entry, will be a transient entry containing an error value (that
    -- appears as an EdhNamedValue) if failed loading, or a permanent
    -- entry containing the module object if successfully loaded
  , edh'world'modules :: !(TMVar (Map.HashMap ModuleId (TMVar EdhValue)))
    -- | for console logging, input and output
  , edh'world'console :: !EdhConsole
  }
instance Eq EdhWorld where
  EdhWorld x'root _ _ _ == EdhWorld y'root _ _ _ =
    edh'scope'this x'root == edh'scope'this y'root

type ModuleId = Text

worldContext :: EdhWorld -> Context
worldContext !world = Context
  { edh'ctx'world        = world
  , edh'ctx'stack        = edh'world'root world :| []
  , edh'ctx'genr'caller  = Nothing
  , edh'ctx'match        = true
  , edh'ctx'stmt         = StmtSrc
                             ( SourcePos { sourceName   = "<genesis>"
                                         , sourceLine   = mkPos 1
                                         , sourceColumn = mkPos 1
                                         }
                             , VoidStmt
                             )
  , edh'ctx'pure         = False
  , edh'ctx'exporting    = False
  , edh'ctx'eff'defining = False
  }
{-# INLINE worldContext #-}


-- | Checkout 'defaultEdhConsole' and 'defaultEdhIOLoop' from the
-- default batteries for implementation details, or just use that.
data EdhConsole = EdhConsole {
    consoleIO :: !(TBQueue EdhConsoleIO)
  , consoleIOLoop :: IO ()
  , consoleLogLevel :: !LogLevel
  , consoleLogger :: !EdhLogger
  , consoleFlush :: IO ()
  }
data EdhConsoleIO = ConsoleShutdown
    | ConsoleOut !Text -- ^ output a line
    | ConsoleIn !(TMVar EdhInput) !Text !Text
    -- ^ read input into the var, with ps1 ps2
    --   ps1 is single line prompt, ps2 for multil-line
  deriving (Eq)
data EdhInput = EdhInput {
    edh'input'src'name :: !Text
  , edh'input'1st'line :: !Int
  , edh'input'src'lines :: ![Text]
  } deriving (Eq, Show)
type EdhLogger = LogLevel -> Maybe String -> ArgsPack -> STM ()
type LogLevel = Int


-- | The states of a thread of an Edh program
data EdhThreadState = EdhThreadState {
    edh'in'tx :: !Bool
  , edh'task'queue :: !(TBQueue EdhTask)
  , edh'perceivers :: !(TVar [PerceiveRecord])
  , edh'defers :: !(TVar [DeferRecord])
  , edh'context :: !Context
  , edh'fork'queue :: !(TBQueue (EdhThreadState, EdhThreadState -> STM ()))
  }

-- | The task to be queued for execution of an Edh thread
--
-- the thread state provides the context, into which an exception should be
-- thrown, if one ever occurs during the action
data EdhTask =
    EdhDoIO  !EdhThreadState !(IO ())
  | EdhDoSTM !EdhThreadState !(STM ())
data PerceiveRecord  = PerceiveRecord
  -- | chan subscribed to source event sink
  !(TChan EdhValue)
  -- | origin ets upon the perceiver is armed
  !EdhThreadState
  -- | reacting action per event received, event value is context match
  !(EdhThreadState -> TVar Bool -> STM ())
data DeferRecord = DeferRecord
  -- | origin ets upon the deferred action is scheduled
  !EdhThreadState
  -- | deferred action to be performed upon termination of the target Edh
  -- thread
  !(EdhThreadState -> STM ())

-- | Construct an call context from thread state
getEdhCallContext :: Int -> EdhThreadState -> EdhCallContext
getEdhCallContext !unwind !pgs = EdhCallContext
  (T.pack $ sourcePosPretty tip)
  frames
 where
  unwindStack :: Int -> [Scope] -> [Scope]
  unwindStack c s | c <= 0 = s
  unwindStack _ []         = []
  unwindStack _ [f    ]    = [f]
  unwindStack c (_ : s)    = unwindStack (c - 1) s
  !ctx                = edh'context pgs
  (StmtSrc (!tip, _)) = edh'ctx'stmt ctx
  !frames =
    foldl'
        (\sfs (Scope _ _ _ _ pd@(ProcDefi _ _ _ (ProcDecl _ _ !procBody)) (StmtSrc (!callerPos, _)) _) ->
          EdhCallFrame (procedureName pd)
                       (procSrcLoc procBody)
                       (T.pack $ sourcePosPretty callerPos)
            : sfs
        )
        []
      $ unwindStack unwind
      $ NE.init (edh'ctx'stack ctx)
  procSrcLoc :: Either StmtSrc EdhProcedure -> Text
  procSrcLoc !procBody = case procBody of
    Left  (StmtSrc (spos, _)) -> T.pack (sourcePosPretty spos)
    Right _                   -> "<host-code>"


-- | Schedule forking of a GHC thread for an Edh thread
--
-- NOTE this happens as part of current STM tx, the actual fork won't happen if
--      any subsequent Edh code within the tx throws without recovered
forkEdh :: EdhThreadState -> EdhProc -> STM ()
forkEdh !etsForker !p = writeTBQueue (edh'fork'queue etsForker) (etsForker, p)
{-# INLINE forkEdh #-}

-- | Schedule an STM action to be performed in current Edh thread, but after
-- current STM tx committed, and after some txs, those possibly already
-- scheduled
--
-- NOTE this happens as part of current STM tx, so the actual action won't be
--      scheduled if any subsequent Edh code within the tx throws without
--      recovered
-- CAVEAT pay special attention in using this, to not break the semantics of
--       `ai` keyword at scripting level
edhContSTM :: EdhThreadState -> STM () -> STM ()
edhContSTM !ets !actSTM =
  writeTBQueue (edh'task'queue ets) $ EdhDoSTM ets actSTM
{-# INLINE edhContSTM #-}

-- | Schedule an IO action to be performed in current Edh thread, but after
-- current STM tx committed, and after some txs, those possibly already
-- scheduled
--
-- NOTE this happens as part of current STM tx, so the actual action won't be
--      scheduled if any subsequent Edh code within the tx throws without
--      recovered
-- CAVEAT pay special attention in using this, to not break the semantics of
--       `ai` keyword at scripting level
edhContIO :: EdhThreadState -> IO () -> STM ()
edhContIO !ets !actIO = writeTBQueue (edh'task'queue ets) $ EdhDoIO ets actIO
{-# INLINE edhContIO #-}


type EdhExit = EdhValue -> STM ()

endOfEdh :: EdhExit
endOfEdh _ = return ()
{-# INLINE endOfEdh #-}

-- | Exit an Edh proc in CPS
--
-- @edh'in'tx ets@ is normally controlled by the `ai` keyword at scripting
-- level, this implements the semantics of it
exitEdh :: EdhThreadState -> EdhExit -> EdhValue -> STM ()
exitEdh !ets !exit !val = if edh'in'tx ets
  then exit val
  else writeTBQueue (edh'task'queue ets) $ EdhDoSTM ets $ exit val
{-# INLINE exitEdh #-}


-- | Somewhat similar to @ 'ReaderT' 'EdhThreadState' 'STM' @, but not
-- monadic
type EdhProc = EdhThreadState -> STM ()

exitEdhProc :: EdhExit -> EdhValue -> EdhProc
exitEdhProc !exit !val !ets = if edh'in'tx ets
  then exit val
  else writeTBQueue (edh'task'queue ets) $ EdhDoSTM ets $ exit val
{-# INLINE exitEdhProc #-}

runEdhProc :: EdhThreadState -> EdhProc -> STM ()
runEdhProc !ets !p = p ets
{-# INLINE runEdhProc #-}


-- | Type for a procedure in host language that can be called from Edh code.
--
-- Note the top frame of the call stack from thread state is the one for the
-- callee, that scope should have mounted the caller's scope entity, not a new
-- entity in contrast to when an Edh procedure as the callee.
type EdhProcedure -- such a procedure servs as the callee
  =  ArgsPack    -- ^ the pack of arguments
  -> EdhExit -- ^ the CPS exit to return a value from this procedure
  -> EdhProc

-- | A no-operation as an Edh procedure, ignoring any arg
edhNop :: EdhProcedure
edhNop _ !exit !ets = exitEdh ets exit nil
{-# INLINE edhNop #-}


-- | Type of an intrinsic infix operator in host language.
--
-- Note no stack frame is created/pushed when an intrinsic operator is called.
type EdhIntrinsicOp = Expr -> Expr -> EdhExit -> EdhProc

data IntrinOpDefi = IntrinOpDefi {
    intrinsic'op'uniq :: !Unique
  , intrinsic'op'symbol :: !AttrName
  , intrinsic'op :: EdhIntrinsicOp
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

-- | Fork a new Edh thread to run the specified event producer, but hold the 
-- production until current thread has later started consuming events from the
-- sink returned here.
launchEventProducer :: EdhExit -> EventSink -> EdhProc -> EdhProc
launchEventProducer !exit sink@(EventSink _ _ _ _ !subc) !producerProg !etsConsumer
  = do
    subcBefore <- readTVar subc
    forkEdh etsConsumer $ \ !etsProducer -> do
      subcNow <- readTVar subc
      when (subcNow == subcBefore) retry
      producerProg etsProducer
    exitEdh etsConsumer exit $ EdhSink sink


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

  -- * term values (immutable)
    | EdhNil
    | EdhDecimal !Decimal
    | EdhBool !Bool
    | EdhBlob !ByteString
    | EdhString !Text
    | EdhSymbol !Symbol
    | EdhUUID !UUID.UUID

  -- * immutable containers
  --   the elements may still pointer to mutable data
    | EdhPair !EdhValue !EdhValue
    | EdhArgsPack ArgsPack

  -- | mutable containers
    | EdhDict !Dict
    | EdhList !List

  -- | an Edh object can either be an entity backed by a hash store, or
  -- wraps some host data dynamically mutable
    | EdhObject !Object

  -- * executable precedures
    | EdhIntrOp !Precedence !IntrinOpDefi
    | EdhMethod !ProcDefi
    | EdhOprtor !Precedence !(Maybe EdhValue) !ProcDefi
    | EdhGnrtor !ProcDefi
    | EdhIntrpr !ProcDefi
    | EdhPrducr !ProcDefi

  -- similar to Python Descriptor
  -- with a getter method and optionally a settor method, for properties
  -- (programmatically managed attributes) to be defined on objects
  -- deleter semantic is expressed as calling setter without arg
    | EdhDescriptor !ProcDefi !(Maybe ProcDefi)

  -- * flow control
    | EdhBreak
    | EdhContinue
    | EdhCaseClose !EdhValue
    | EdhCaseOther
    | EdhFallthrough
    | EdhRethrow
    | EdhYield !EdhValue
    | EdhReturn !EdhValue

  -- | prefer better efforted result, but can default to the specified expr
  -- if there's no better result applicable
  -- 
  -- this is used to signal try-next-impl semantics similar to NotImplemented
  -- in Python.
  --
  -- `return default { throw xxx }` can be used to signal that it has to have
  -- some more concrete implementation;
  -- and `return default { pass }` can be used to prefer an even more deferred
  -- default if any exists, or `nil` if none.
    | EdhDefault !Unique !Expr !(Maybe EdhThreadState)

  -- | event sink
    | EdhSink !EventSink

  -- | named value, a.k.a. term definition
    | EdhNamedValue !AttrName !EdhValue

  -- | reflective expr, with source (or not, if empty)
    | EdhExpr !Unique !Expr !Text

instance Show EdhValue where
  show (EdhType t)     = show t
  show EdhNil          = "nil"
  show (EdhDecimal v ) = showDecimal v
  show (EdhBool    v ) = if v then "true" else "false"
  show (EdhBlob    b ) = "<blob#" <> show (B.length b) <> ">"
  show (EdhString  v ) = show v
  show (EdhSymbol  v ) = show v
  show (EdhUUID    v ) = "UUID('" <> UUID.toString v <> "')"

  show (EdhObject  v ) = show v

  show (EdhDict    v ) = show v
  show (EdhList    v ) = show v

  show (EdhPair k v  ) = show k <> ":" <> show v
  show (EdhArgsPack v) = show v

  show (EdhIntrOp !preced (IntrinOpDefi _ !opSym _)) =
    "<intrinsic: (" ++ T.unpack opSym ++ ") " ++ show preced ++ ">"
  show (EdhMethod !pd) = T.unpack (procedureName pd)
  show (EdhOprtor !preced _ !pd) =
    "<operator: (" ++ T.unpack (procedureName pd) ++ ") " ++ show preced ++ ">"
  show (EdhGnrtor !pd) = T.unpack (procedureName pd)
  show (EdhIntrpr !pd) = T.unpack (procedureName pd)
  show (EdhPrducr !pd) = T.unpack (procedureName pd)

  show (EdhDescriptor !getter !setter) =
    (<> T.unpack (procedureName getter) <> ">") $ case setter of
      Nothing -> "<readonly property "
      Just _  -> "<property "

  show EdhBreak           = "<break>"
  show EdhContinue        = "<continue>"
  show (EdhCaseClose v)   = "<caseclose: " ++ show v ++ ">"
  show EdhCaseOther       = "<caseother>"
  show EdhFallthrough     = "<fallthrough>"
  show EdhRethrow         = "<rethrow>"
  show (EdhYield  v     ) = "<yield: " ++ show v ++ ">"
  show (EdhReturn v     ) = "<return: " ++ show v ++ ">"
  show (EdhDefault _ x _) = "<default: " ++ show x ++ ">"

  show (EdhSink v       ) = show v

  show (EdhNamedValue n v@EdhNamedValue{}) =
    -- Edh operators are all left-associative, parenthesis needed
    T.unpack n <> " := (" <> show v <> ")"
  show (EdhNamedValue n v) = T.unpack n <> " := " <> show v

  show (EdhExpr _ x s    ) = if T.null s
    then -- source-less form
         "<expr: " ++ show x ++ ">"
    else -- source-ful form
         T.unpack s

-- Note:
--
-- here is identity-wise equality i.e. pointer equality if mutable,
-- or value equality if immutable.
--
-- the semantics are different from value-wise equality especially
-- for types of:  object/dict/list

instance Eq EdhValue where
  EdhType x       == EdhType y       = x == y
  EdhNil          == EdhNil          = True
  EdhDecimal x    == EdhDecimal y    = x == y
  EdhBool    x    == EdhBool    y    = x == y
  EdhBlob    x    == EdhBlob    y    = x == y
  EdhString  x    == EdhString  y    = x == y
  EdhSymbol  x    == EdhSymbol  y    = x == y
  EdhUUID    x    == EdhUUID    y    = x == y

  EdhObject  x    == EdhObject  y    = x == y

  EdhDict    x    == EdhDict    y    = x == y
  EdhList    x    == EdhList    y    = x == y
  EdhPair x'k x'v == EdhPair y'k y'v = x'k == y'k && x'v == y'v
  EdhArgsPack x   == EdhArgsPack y   = x == y

  EdhIntrOp _ (IntrinOpDefi x'u _ _) == EdhIntrOp _ (IntrinOpDefi y'u _ _) =
    x'u == y'u
  EdhMethod x     == EdhMethod y     = x == y
  EdhOprtor _ _ x == EdhOprtor _ _ y = x == y
  EdhGnrtor x     == EdhGnrtor y     = x == y
  EdhIntrpr x     == EdhIntrpr y     = x == y
  EdhPrducr x     == EdhPrducr y     = x == y

  EdhDescriptor x'getter x'setter == EdhDescriptor y'getter y'setter =
    x'getter == y'getter && x'setter == y'setter

  EdhBreak                    == EdhBreak                    = True
  EdhContinue                 == EdhContinue                 = True
  EdhCaseClose x              == EdhCaseClose y              = x == y
  EdhCaseOther                == EdhCaseOther                = True
  EdhFallthrough              == EdhFallthrough              = True
  EdhRethrow                  == EdhRethrow                  = True
-- todo: regard a yielded/returned value equal to the value itself ?
  EdhYield  x'v               == EdhYield  y'v               = x'v == y'v
  EdhReturn x'v               == EdhReturn y'v               = x'v == y'v
  EdhDefault x'u _ _          == EdhDefault y'u _ _          = x'u == y'u

  EdhSink x                   == EdhSink y                   = x == y

  EdhNamedValue _ x'v         == EdhNamedValue _ y'v         = x'v == y'v
  EdhNamedValue _ x'v         == y                           = x'v == y
  x                           == EdhNamedValue _ y'v         = x == y'v

  EdhExpr _   (LitExpr x'l) _ == EdhExpr _   (LitExpr y'l) _ = x'l == y'l
  EdhExpr x'u _             _ == EdhExpr y'u _             _ = x'u == y'u

-- todo: support coercing equality ?
--       * without this, we are a strongly typed dynamic language
--       * with this, we'll be a weakly typed dynamic language
  _                           == _                           = False

instance Hashable EdhValue where
  hashWithSalt s (EdhType x) = hashWithSalt s $ 1 + fromEnum x
  hashWithSalt s EdhNil = hashWithSalt s (0 :: Int)
  hashWithSalt s (EdhDecimal x                      ) = hashWithSalt s x
  hashWithSalt s (EdhBool    x                      ) = hashWithSalt s x
  hashWithSalt s (EdhBlob    x                      ) = hashWithSalt s x
  hashWithSalt s (EdhString  x                      ) = hashWithSalt s x
  hashWithSalt s (EdhSymbol  x                      ) = hashWithSalt s x
  hashWithSalt s (EdhUUID    x                      ) = hashWithSalt s x
  hashWithSalt s (EdhObject  x                      ) = hashWithSalt s x

  hashWithSalt s (EdhDict    x                      ) = hashWithSalt s x
  hashWithSalt s (EdhList    x                      ) = hashWithSalt s x
  hashWithSalt s (EdhPair k v) = s `hashWithSalt` k `hashWithSalt` v
  hashWithSalt s (EdhArgsPack x                     ) = hashWithSalt s x

  hashWithSalt s (EdhIntrOp _ (IntrinOpDefi x'u _ _)) = hashWithSalt s x'u
  hashWithSalt s (EdhMethod x                       ) = hashWithSalt s x
  hashWithSalt s (EdhOprtor _ _ x                   ) = hashWithSalt s x
  hashWithSalt s (EdhGnrtor x                       ) = hashWithSalt s x
  hashWithSalt s (EdhIntrpr x                       ) = hashWithSalt s x
  hashWithSalt s (EdhPrducr x                       ) = hashWithSalt s x

  hashWithSalt s (EdhDescriptor getter setter) =
    s `hashWithSalt` getter `hashWithSalt` setter

  hashWithSalt s EdhBreak    = hashWithSalt s (-1 :: Int)
  hashWithSalt s EdhContinue = hashWithSalt s (-2 :: Int)
  hashWithSalt s (EdhCaseClose v) =
    s `hashWithSalt` (-3 :: Int) `hashWithSalt` v
  hashWithSalt s EdhCaseOther   = hashWithSalt s (-4 :: Int)
  hashWithSalt s EdhFallthrough = hashWithSalt s (-5 :: Int)
  hashWithSalt s EdhRethrow     = hashWithSalt s (-6 :: Int)
  hashWithSalt s (EdhYield  v)  = s `hashWithSalt` (-7 :: Int) `hashWithSalt` v
  hashWithSalt s (EdhReturn v)  = s `hashWithSalt` (-8 :: Int) `hashWithSalt` v
  hashWithSalt s (EdhDefault u _ _) =
    s `hashWithSalt` (-9 :: Int) `hashWithSalt` u

  hashWithSalt s (EdhSink x              ) = hashWithSalt s x

  hashWithSalt s (EdhNamedValue _ v      ) = hashWithSalt s v

  hashWithSalt s (EdhExpr _ (LitExpr l) _) = hashWithSalt s l
  hashWithSalt s (EdhExpr u _           _) = hashWithSalt s u


edhDeCaseClose :: EdhValue -> EdhValue
edhDeCaseClose (EdhCaseClose !val) = edhDeCaseClose val
edhDeCaseClose !val                = val

edhUltimate :: EdhValue -> EdhValue
edhUltimate (EdhNamedValue _ v) = edhDeCaseClose v
edhUltimate (EdhReturn v      ) = edhDeCaseClose v
edhUltimate (EdhYield  v      ) = edhDeCaseClose v
edhUltimate v                   = edhDeCaseClose v


nil :: EdhValue
nil = EdhNil

-- | Resembles `None` as in Python
--
-- assigning to `nil` in Edh is roughly the same of `delete` as
-- in JavaScript, and `del` as in Python. Assigning to `None`
-- will keep the dict entry or object attribute while still
-- carrying a semantic of *absence*.
edhNone :: EdhValue
edhNone = EdhNamedValue "None" EdhNil

-- | None as an expression
edhNoneExpr :: Expr
edhNoneExpr =
  InfixExpr ":=" (AttrExpr (DirectRef (NamedAttr "None"))) (LitExpr NilLiteral)

-- | Similar to `None`
--
-- though we don't have `Maybe` monad in Edh, having a `Nothing`
-- carrying null semantic may be useful in some cases.
edhNothing :: EdhValue
edhNothing = EdhNamedValue "Nothing" EdhNil

-- | Nothing as an expression
edhNothingExpr :: Expr
edhNothingExpr = InfixExpr ":="
                           (AttrExpr (DirectRef (NamedAttr "Nothing")))
                           (LitExpr NilLiteral)

-- | With `nil` converted to `None` so the result will never be `nil`.
--
-- As `nil` carries *delete* semantic in assignment, in some cases it's better
-- avoided.
noneNil :: EdhValue -> EdhValue
noneNil EdhNil = edhNone
noneNil !v     = v

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
  StmtSrc (x'sp, _) == StmtSrc (y'sp, _) = x'sp == y'sp
instance Show StmtSrc where
  show (StmtSrc (_sp, stmt)) = show stmt


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
      -- | artifacts introduced within an `effect` statement will be put
      -- into effect namespace, which as currently implemented, a dict
      -- resides in current scope entity addressed by name `__exports__`
    | EffectStmt !Expr
      -- | assignment with args (un/re)pack sending/receiving syntax
    | LetStmt !ArgsReceiver !ArgsPacker
      -- | super object declaration for a descendant object
    | ExtendsStmt !Expr
      -- | perceiption declaration, a perceiver is bound to an event `sink`
      -- with the calling thread as context, when an event fires from that
      -- event `sink`, the bound perceiver body will be executed from the
      -- thread where it's declared, after the currernt transaction on that
      -- thread finishes, a perceiver body can `break` to terminate that
      -- particular thread, or the thread will continue to process next
      -- perceiver, if no perceiver does `break`, next transactional task
      -- is carried on as normally.
      --
      -- the perceiver body uses a value/pattern matching branch, or a
      -- group of branches (as a block expr) to handle the happened event
      -- data, including `nil` as end-of-stream indicator.
      --
      -- the perceiption construct is somewhat similar to traditional signal
      -- handling mechanism in OS process management
    | PerceiveStmt !Expr !Expr
      -- | while loop
    | WhileStmt !Expr !StmtSrc
      -- | break from a while/for loop, or terminate the Edh thread if given
      -- from a perceiver
    | BreakStmt
      -- | continue a while/for loop
    | ContinueStmt
      -- | similar to fallthrough in Go
    | FallthroughStmt
      -- | rethrow current exception
    | RethrowStmt
      -- | any value can be thrown as exception, handling will rely on the
      --   ($=>) as `catch` and (@=>) as `finally` operators
    | ThrowStmt !Expr
      -- | early stop from a procedure
    | ReturnStmt !Expr
      -- | expression with precedence
    | ExprStmt !Expr
  deriving (Show)

-- Attribute addressor
data AttrAddr = ThisRef | ThatRef | SuperRef
    | DirectRef !AttrAddressor
    | IndirectRef !Expr !AttrAddressor
  deriving (Eq, Show)

-- | the key to address attributes against a left hand entity object or
-- current scope
data AttrAddressor =
    -- | vanilla form, by alphanumeric name
    NamedAttr !AttrName
    -- | get the symbol value from current scope,
    -- then use it to address attributes
    | SymbolicAttr !AttrName
  deriving (Eq)
instance Show AttrAddressor where
  show (NamedAttr    n) = T.unpack n
  show (SymbolicAttr s) = "@" <> T.unpack s
instance Hashable AttrAddressor where
  hashWithSalt s (NamedAttr name) = s `hashWithSalt` name
  hashWithSalt s (SymbolicAttr sym) =
    s `hashWithSalt` ("@" :: Text) `hashWithSalt` sym


receivesNamedArg :: Text -> ArgsReceiver -> Bool
receivesNamedArg _     WildReceiver              = True
receivesNamedArg !name (SingleReceiver argRcvr ) = _hasNamedArg name [argRcvr]
receivesNamedArg !name (PackReceiver   argRcvrs) = _hasNamedArg name argRcvrs

_hasNamedArg :: Text -> [ArgReceiver] -> Bool
_hasNamedArg _     []           = False
_hasNamedArg !name (arg : rest) = case arg of
  RecvArg (NamedAttr !argName) _ _ -> argName == name || _hasNamedArg name rest
  _ -> _hasNamedArg name rest

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
    | RecvArg !AttrAddressor !(Maybe AttrAddr) !(Maybe Expr)
  deriving (Eq)
instance Show ArgReceiver where
  show (RecvRestPosArgs nm) = "*" ++ T.unpack nm
  show (RecvRestKwArgs  nm) = "**" ++ T.unpack nm
  show (RecvRestPkArgs  nm) = "***" ++ T.unpack nm
  show (RecvArg nm _ _    ) = show nm

mandatoryArg :: AttrName -> ArgReceiver
mandatoryArg !name = RecvArg (NamedAttr name) Nothing Nothing

optionalArg :: AttrName -> Expr -> ArgReceiver
optionalArg !name !defExpr = RecvArg (NamedAttr name) Nothing (Just defExpr)


type ArgsPacker = [ArgSender]
data ArgSender = UnpackPosArgs !Expr
    | UnpackKwArgs !Expr
    | UnpackPkArgs !Expr
    | SendPosArg !Expr
    | SendKwArg !AttrAddressor !Expr
  deriving (Eq, Show)

-- | Procedure declaration, result of parsing
data ProcDecl = ProcDecl {
    edh'procedure'addr :: !AttrAddressor
  , edh'procedure'args :: !ArgsReceiver
  , edh'procedure'body :: !(Either StmtSrc EdhProcedure)
  }
instance Eq ProcDecl where
  ProcDecl{} == ProcDecl{} = False
instance Show ProcDecl where
  show (ProcDecl !addr _ !pb) = case pb of
    Left  _ -> "<edh-proc " <> show addr <> ">"
    Right _ -> "<host-proc " <> show addr <> ">"


-- | Procedure definition, result of execution of the declaration
data ProcDefi = ProcDefi {
    edh'procedure'ident :: !Unique
  , edh'procedure'name :: !AttrKey
  , edh'procedure'lexi :: !Scope
  , edh'procedure'decl :: {-# UNPACK #-} !ProcDecl
  }
instance Eq ProcDefi where
  ProcDefi x'u _ _ _ == ProcDefi y'u _ _ _ = x'u == y'u
instance Ord ProcDefi where
  compare (ProcDefi x'u _ _ _) (ProcDefi y'u _ _ _) = compare x'u y'u
instance Hashable ProcDefi where
  hashWithSalt s (ProcDefi u _ _ _) = s `hashWithSalt` u
instance Show ProcDefi where
  show (ProcDefi _ !name _ (ProcDecl !addr _ !pb)) = case pb of
    Left  _ -> "<edh-proc " <> show name <> " : " <> show addr <> ">"
    Right _ -> "<host-proc " <> show name <> " : " <> show addr <> ">"

procedureName :: ProcDefi -> Text
procedureName !pd = case edh'procedure'name pd of
  AttrByName !n            -> n
  AttrBySym  (Symbol _ !r) -> r


data Prefix = PrefixPlus | PrefixMinus | Not
    -- | to disregard the match target in context,
    -- for a branch condition
    | Guard
  deriving (Eq, Show)

data DictKeyExpr =
      LitDictKey !Literal
    | AddrDictKey !AttrAddr
    | ExprDictKey !Expr -- this must be quoted in parenthesis
  deriving (Eq, Show)

data Expr = LitExpr !Literal | PrefixExpr !Prefix !Expr
    | IfExpr { if'condition :: !Expr
            , if'consequence :: !Expr
            , if'alternative :: !(Maybe Expr)
            }
    | CaseExpr { case'target :: !Expr , case'branches :: !Expr }

      -- note: the order of entries is reversed as parsed from source
    | DictExpr ![(DictKeyExpr, Expr)]
    | ListExpr ![Expr]
    | ArgsPackExpr !ArgsPacker
    | ParenExpr !Expr

      -- | import with args (re)pack receiving syntax
      -- `into` a target object from specified expr, or current scope
    | ImportExpr !ArgsReceiver !Expr !(Maybe Expr)
      -- | only artifacts introduced within an `export` statement, into
      -- `this` object in context, are eligible for importing by others
    | ExportExpr !Expr
      -- | namespace object creation
    | NamespaceExpr !ProcDecl !ArgsPacker
      -- | class (constructor) procedure definition
    | ClassExpr !ProcDecl
      -- | method procedure definition
    | MethodExpr !ProcDecl
      -- | generator procedure definition
    | GeneratorExpr !ProcDecl
      -- | interpreter declaration, an interpreter procedure is not otherwise
      -- different from a method procedure, except it receives arguments
      -- in expression form rather than values, in addition to the reflective
      -- `callerScope` as first argument
    | InterpreterExpr !ProcDecl
    | ProducerExpr !ProcDecl
      -- | operator declaration
    | OpDeclExpr !OpSymbol !Precedence !ProcDecl
      -- | operator override
    | OpOvrdExpr !OpSymbol !ProcDecl !Precedence

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
    -- then the curly brackets can be used to quote a statement into an
    -- expression, e.g. so that a method procedure can explicitly
    -- `return { continue }` to carry a semantic to the magic method
    -- caller that it should try next method, similar to what
    -- `NotImplemented` does in Python.
    | BlockExpr ![StmtSrc]

    | YieldExpr !Expr

    -- | a for-from-do loop is made an expression in Edh, so it can
    -- appear as the right-hand expr of the comprehension (=<) operator.
    | ForExpr !ArgsReceiver !Expr !Expr

    -- | call out an effectful artifact, search only outer stack frames,
    -- if from an effectful procedure run
    | PerformExpr !AttrAddressor
    -- | call out an effectful artifact, always search full stack frames
    | BehaveExpr !AttrAddressor

    | AttrExpr !AttrAddr
    | IndexExpr { index'value :: !Expr
                , index'target :: !Expr
                }
    | CallExpr !Expr !ArgsPacker

    | InfixExpr !OpSymbol !Expr !Expr

    -- specify a default by Edh code
    | DefaultExpr !Expr

    -- to support interpolation within expressions, with source form
    | ExprWithSrc !Expr ![SourceSeg]
    | IntplExpr !Expr
    | IntplSubs !EdhValue
  deriving (Eq, Show)

data SourceSeg = SrcSeg !Text | IntplSeg !Expr
  deriving (Eq, Show)

data Literal = SinkCtor
    | NilLiteral
    | DecLiteral !Decimal
    | BoolLiteral !Bool
    | StringLiteral !Text
    | TypeLiteral !EdhTypeValue
  deriving (Eq, Show)
instance Hashable Literal where
  hashWithSalt s SinkCtor          = hashWithSalt s (-1 :: Int)
  hashWithSalt s NilLiteral        = hashWithSalt s (0 :: Int)
  hashWithSalt s (DecLiteral    x) = hashWithSalt s x
  hashWithSalt s (BoolLiteral   x) = hashWithSalt s x
  hashWithSalt s (StringLiteral x) = hashWithSalt s x
  hashWithSalt s (TypeLiteral   x) = hashWithSalt s x


-- | the type for the value of type of a value
data EdhTypeValue = TypeType
    -- nil has no type, its type if you really ask, is nil
    | DecimalType
    | BoolType
    | StringType
    | BlobType
    | SymbolType
    | UUIDType
    | ObjectType
    | DictType
    | ListType
    | PairType
    | ArgsPackType
    | BlockType
    | HostClassType
    | HostMethodType
    | HostOperType
    | HostGenrType
    | IntrinsicType
    | ClassType
    | MethodType
    | OperatorType
    | GeneratorType
    | InterpreterType
    | ProducerType
    | DescriptorType
    | BreakType
    | ContinueType
    | CaseCloseType
    | CaseOtherType
    | FallthroughType
    | RethrowType
    | YieldType
    | ReturnType
    | DefaultType
    | SinkType
    | ExprType
  deriving (Enum, Eq, Ord, Show)
instance Hashable EdhTypeValue where
  hashWithSalt s t = hashWithSalt s $ fromEnum t

edhTypeNameOf :: EdhValue -> String
edhTypeNameOf EdhNil                   = "nil"
edhTypeNameOf (EdhNamedValue n EdhNil) = T.unpack n
edhTypeNameOf (EdhNamedValue n v) =
  T.unpack n <> " := " <> show (edhTypeNameOf v)
edhTypeNameOf v = show $ edhTypeOf v

-- | Get the type tag of an value
--
-- Passing in a `nil` value will hit bottom (crash the process) here,
-- use `edhTypeNameOf` if all you want is a type name shown to user.
edhTypeOf :: EdhValue -> EdhTypeValue

-- it's a taboo to get the type of a nil, either named or not
edhTypeOf EdhNil                   = undefined
edhTypeOf (EdhNamedValue _ EdhNil) = undefined

edhTypeOf EdhType{}                = TypeType

edhTypeOf EdhDecimal{}             = DecimalType
edhTypeOf EdhBool{}                = BoolType
edhTypeOf EdhBlob{}                = BlobType
edhTypeOf EdhString{}              = StringType
edhTypeOf EdhSymbol{}              = SymbolType
edhTypeOf EdhUUID{}                = UUIDType
edhTypeOf (EdhObject o)            = case edh'obj'store o of
  HashStore{} -> ObjectType
  ClassStore (Class pd _ _) ->
    case edh'procedure'body $ edh'procedure'decl pd of
      Left{}  -> ClassType
      Right{} -> HostClassType
  HostStore{} -> ObjectType -- TODO add a @HostObjectType@ to distinguish?
edhTypeOf EdhDict{}     = DictType
edhTypeOf EdhList{}     = ListType
edhTypeOf EdhPair{}     = PairType
edhTypeOf EdhArgsPack{} = ArgsPackType

edhTypeOf EdhIntrOp{}   = IntrinsicType
edhTypeOf (EdhMethod (ProcDefi _ _ _ (ProcDecl _ _ pb))) = case pb of
  Left  _ -> MethodType
  Right _ -> HostMethodType
edhTypeOf (EdhOprtor _ _ (ProcDefi _ _ _ (ProcDecl _ _ pb))) = case pb of
  Left  _ -> OperatorType
  Right _ -> HostOperType
edhTypeOf (EdhGnrtor (ProcDefi _ _ _ (ProcDecl _ _ pb))) = case pb of
  Left  _ -> GeneratorType
  Right _ -> HostGenrType

edhTypeOf EdhDescriptor{}     = DescriptorType

edhTypeOf EdhIntrpr{}         = InterpreterType
edhTypeOf EdhPrducr{}         = ProducerType
edhTypeOf EdhBreak            = BreakType
edhTypeOf EdhContinue         = ContinueType
edhTypeOf EdhCaseClose{}      = CaseCloseType
edhTypeOf EdhCaseOther        = CaseOtherType
edhTypeOf EdhFallthrough      = FallthroughType
edhTypeOf EdhRethrow          = RethrowType
edhTypeOf EdhYield{}          = YieldType
edhTypeOf EdhReturn{}         = ReturnType
edhTypeOf EdhDefault{}        = DefaultType
edhTypeOf EdhSink{}           = SinkType
edhTypeOf (EdhNamedValue _ v) = edhTypeOf v
edhTypeOf EdhExpr{}           = ExprType


mkIntrinsicOp :: EdhWorld -> OpSymbol -> EdhIntrinsicOp -> STM EdhValue
mkIntrinsicOp !world !opSym !iop = do
  u <- unsafeIOToSTM newUnique
  Map.lookup opSym <$> readTMVar (edh'world'operators world) >>= \case
    Nothing ->
      throwSTM
        $ EdhError
            UsageError
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
    { edh'procedure'ident = u
    , edh'procedure'name  = AttrByName nm
    , edh'procedure'lexi  = scope
    , edh'procedure'decl  = ProcDecl { edh'procedure'addr = NamedAttr nm
                                     , edh'procedure'args = args
                                     , edh'procedure'body = Right p
                                     }
    }

mkSymbolicHostProc
  :: Scope
  -> (ProcDefi -> EdhValue)
  -> Symbol
  -> EdhProcedure
  -> ArgsReceiver
  -> STM EdhValue
mkSymbolicHostProc !scope !vc !sym !p !args = do
  u <- unsafeIOToSTM newUnique
  return $ vc ProcDefi
    { edh'procedure'ident = u
    , edh'procedure'name  = AttrBySym sym
    , edh'procedure'lexi  = scope
    , edh'procedure'decl  = ProcDecl
                              { edh'procedure'addr = SymbolicAttr
                                                       $ symbolName sym
                              , edh'procedure'args = args
                              , edh'procedure'body = Right p
                              }
    }


mkHostProperty
  :: Scope -> Text -> EdhProcedure -> Maybe EdhProcedure -> STM EdhValue
mkHostProperty !scope !nm !getterProc !maybeSetterProc = do
  getter <- do
    u <- unsafeIOToSTM newUnique
    return $ ProcDefi
      { edh'procedure'ident = u
      , edh'procedure'name  = AttrByName nm
      , edh'procedure'lexi  = scope
      , edh'procedure'decl  = ProcDecl { edh'procedure'addr = NamedAttr nm
                                       , edh'procedure'args = PackReceiver []
                                       , edh'procedure'body = Right getterProc
                                       }
      }
  setter <- case maybeSetterProc of
    Nothing          -> return Nothing
    Just !setterProc -> do
      u <- unsafeIOToSTM newUnique
      return $ Just $ ProcDefi
        { edh'procedure'ident = u
        , edh'procedure'name  = AttrByName nm
        , edh'procedure'lexi  = scope
        , edh'procedure'decl  = ProcDecl
          { edh'procedure'addr = NamedAttr nm
          , edh'procedure'args = PackReceiver
                                   [optionalArg "newValue" $ LitExpr NilLiteral]
          , edh'procedure'body = Right setterProc
          }
        }
  return $ EdhDescriptor getter setter


-- | A host class procedure run with the class object's static store as
-- contextual scope entity, and the class object as @this/that@ object,
-- it should populate the static attributes for the class, mostly methods,
-- and possibly shared static values for object instances of the class.
--
-- NOTE the class name is available from the contextual procedure definition,
--      which is also the @edh'class'proc@ in the 'Class' record.
type EdhHostClass = STM () -> EdhProc

mkHostClass
  :: EdhThreadState
  -> Text
  -> EdhHostClass
  -> EdhObjectAllocator
  -> (Object -> STM ())
  -> STM ()
mkHostClass !ets !className !hostCtor !allocator !exit = do
  !clsIdent <- unsafeIOToSTM newUnique
  !hsCls    <- iopdEmpty
  !ssCls    <- newTVar []
  let
    clsProc = ProcDefi clsIdent (AttrByName className) scope
      $ ProcDecl (NamedAttr className) (PackReceiver []) (Right edhNop)
    cls      = Class clsProc hsCls allocator
    clsObj   = Object clsIdent (ClassStore cls) metaClassObj ssCls

    clsScope = Scope hsCls
                     clsObj
                     clsObj
                     defaultEdhExcptHndlr
                     clsProc
                     (edh'ctx'stmt ctx)
                     []

    etsCtor = ets
      { edh'context = ctx { edh'ctx'stack = clsScope <| edh'ctx'stack ctx }
      }
  runEdhProc etsCtor $ hostCtor $ exit clsObj
 where
  !ctx   = edh'context ets
  !scope = contextScope ctx
  !metaClassObj =
    edh'obj'class $ edh'scope'this $ edh'world'root $ edh'ctx'world ctx


data EdhIndex = EdhIndex !Int | EdhAny | EdhAll | EdhSlice {
    edh'slice'start :: !(Maybe Int)
  , edh'slice'stop :: !(Maybe Int)
  , edh'slice'step :: !(Maybe Int)
  } deriving (Eq)

