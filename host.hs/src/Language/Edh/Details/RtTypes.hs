{-# LANGUAGE PatternSynonyms #-}

module Language.Edh.Details.RtTypes where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )
import           System.IO.Unsafe               ( unsafePerformIO )

import           Control.Exception
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
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE
import           Data.Dynamic

import qualified Data.UUID                     as UUID
import qualified Data.UUID.V4                  as UUID

import           Text.Megaparsec

import           Data.Lossless.Decimal         as D

import           Language.Edh.Control

import           Language.Edh.Details.IOPD


-- | `nil` carries deletion semantics in Edh
edhSetValue
  :: forall k
   . (Eq k, Hashable k)
  => k
  -> EdhValue
  -> IOPD k EdhValue
  -> STM ()
edhSetValue !key !val !d = case val of
  EdhNil -> iopdDelete key d
  _      -> iopdInsert key val d


-- | A pack of evaluated argument values with positional/keyword origin,
-- this works in places of tuples in other languages, apk in Edh can be
-- considered a tuple if only positional arguments inside.
-- Specifically, an empty apk is just considered an empty tuple.
data ArgsPack = ArgsPack {
    positional'args :: ![EdhValue]
  , keyword'args :: !KwArgs
  } deriving Eq
type KwArgs = (OrderedDict AttrKey EdhValue)
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

-- | Used to declare a repacking receiver
type RestPosArgs = [EdhValue]
-- | Used to declare a repacking receiver
type RestKwArgs = KwArgs
-- | Used to declare a repacking receiver
type RestPackArgs = ArgsPack

-- | Used to declare a positional-only args receiver,
-- disambiguated from a repacking receiver
newtype PositionalArgs = PositionalArgs [EdhValue]
-- | Used to declare a keyword-only args receiver,
-- disambiguated from a repacking receiver
newtype KeywordArgs = KeywordArgs KwArgs
-- | Used to declare an apk receiver,
-- disambiguated from a repacking receiver
newtype PackedArgs = PackedArgs ArgsPack

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
  show = T.unpack . attrKeyStr
instance Hashable AttrKey where
  hashWithSalt s (AttrByName name) =
    s `hashWithSalt` (0 :: Int) `hashWithSalt` name
  hashWithSalt s (AttrBySym sym) =
    s `hashWithSalt` (1 :: Int) `hashWithSalt` sym

type AttrName = Text

attrKeyStr :: AttrKey -> Text
attrKeyStr (AttrByName !nm                ) = nm
attrKeyStr (AttrBySym  (Symbol _ !symRepr)) = symRepr

attrKeyValue :: AttrKey -> EdhValue
attrKeyValue (AttrByName !nm ) = EdhString nm
attrKeyValue (AttrBySym  !sym) = EdhSymbol sym


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


mkDefault :: Expr -> STM EdhValue
mkDefault !x = do
  !u <- unsafeIOToSTM newUnique
  return $ EdhDefault u x Nothing


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

-- the yield receiver, a.k.a. the caller's continuation
type EdhGenrCaller
  =  EdhValue -- ^ one value yielded from the generator
  -> (Either (EdhThreadState, EdhValue) EdhValue -> STM ())
    -- ^ continuation of the genrator
    -- - Left (etsThrower, exv)
    --    exception thrown in processing that `yield`ed value
    -- - Right yieldResult
    --    result given back as the yielded value is processed,
    --    suitable to be the eval result of that `yield` action
  -> STM ()


type EdhExcptHndlr
  =  EdhThreadState       -- ^ thread state of the thrower
  -> EdhValue             -- ^ the error value to handle
  -> (EdhValue -> STM ()) -- ^ action to re-throw if not recovered
  -> STM ()

defaultEdhExcptHndlr :: EdhExcptHndlr
defaultEdhExcptHndlr _etsThrower !exv !rethrow = rethrow exv


-- | Construct an call context from thread state
getEdhCallContext :: Int -> EdhThreadState -> EdhCallContext
getEdhCallContext !unwind !ets = EdhCallContext
  (T.pack $ prettySourceLoc tip)
  frames
 where
  unwindStack :: Int -> [Scope] -> [Scope]
  unwindStack c s | c <= 0 = s
  unwindStack _ []         = []
  unwindStack _ [f    ]    = [f]
  unwindStack c (_ : s)    = unwindStack (c - 1) s
  !ctx                = edh'context ets
  (StmtSrc (!tip, _)) = edh'ctx'stmt ctx
  !frames =
    foldl'
        (\sfs (Scope _ _ _ _ pd@(ProcDefi _ _ _ _ (ProcDecl _ _ !procBody)) (StmtSrc (!callerPos, _)) _) ->
          EdhCallFrame (procedureName pd)
                       (procSrcLoc procBody)
                       (T.pack $ prettySourceLoc callerPos)
            : sfs
        )
        []
      $ unwindStack unwind
      $ NE.init (edh'ctx'stack ctx)
  procSrcLoc :: Either StmtSrc (ArgsPack -> EdhHostProc) -> Text
  procSrcLoc !procBody = case procBody of
    Left  (StmtSrc (spos, _)) -> T.pack (prettySourceLoc spos)
    Right _                   -> "<host-code>"

edhCreateError :: Int -> EdhThreadState -> EdhErrorTag -> ArgsPack -> EdhError
edhCreateError !unwindDef !ets !tag apk@(ArgsPack !args !kwargs) = case args of
  [EdhString !m] | odNull kwargs' -> createErr m nil
  (EdhString !m : args')          -> createErr m $ case args' of
    [] | odNull kwargs' -> nil
    _                   -> EdhArgsPack $ ArgsPack args' kwargs
  _ -> createErr "❌" $ case args of
    [] | odNull kwargs' -> nil
    _                   -> EdhArgsPack apk
 where
  createErr !msg !details = EdhError tag msg (toDyn details) cc
  (!maybeUnwind, !kwargs') = odTakeOut (AttrByName "unwind") kwargs
  !unwind                  = case maybeUnwind of
    Just (EdhDecimal d) -> case decimalToInteger d of
      Just !n -> fromIntegral n
      _       -> unwindDef
    _ -> unwindDef
  !cc = getEdhCallContext unwind ets


-- | A lexical scope
data Scope = Scope {
    -- | the backing storage of this scope
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
    -- | the Edh procedure, as to run which, this scope is created
    -- note this is left lazy so the root scope can be created without infinite
    -- loop
  , edh'scope'proc :: ProcDefi
    -- | the Edh stmt caused creation of this scope
  , edh'scope'caller :: !StmtSrc
    -- | when this scope is of an effectful procedure as called, this is the
    -- outer call stack from which (but not including the) scope the
    -- procedure is addressed of
  , edh'effects'stack :: [Scope]
  }
instance Show Scope where
  show (Scope _ _ _ _ (ProcDefi _ _ _ _ (ProcDecl !addr _ !procBody)) (StmtSrc (!cPos, _)) _)
    = "📜 " ++ show addr ++ " 🔎 " ++ defLoc ++ " 👈 " ++ prettySourceLoc cPos
   where
    defLoc = case procBody of
      Right _                   -> "<host-code>"
      Left  (StmtSrc (dPos, _)) -> prettySourceLoc dPos

outerScopeOf :: Scope -> Maybe Scope
outerScopeOf !scope = if edh'scope'proc outerScope == edh'scope'proc scope
  then Nothing -- already at world root scope
  else Just outerScope
  where !outerScope = edh'procedure'lexi $ edh'scope'proc scope

rootScopeOf :: Scope -> Scope
rootScopeOf !scope = if edh'scope'proc outerScope == edh'scope'proc scope
  then scope -- found world root scope
  else rootScopeOf outerScope
  where !outerScope = edh'procedure'lexi $ edh'scope'proc scope

scopeLexiLoc :: Scope -> (Text -> STM ()) -> STM ()
scopeLexiLoc !scope !exit = case pb of
  Left (StmtSrc (srcLoc, _)) -> exit $ T.pack $ prettySourceLoc srcLoc
  Right{} ->
    iopdLookup (AttrByName "__file__") (edh'scope'entity scope) >>= \case
      Nothing           -> exit $ "<host-procedure: " <> procedureName pd <> ">"
      Just !moduFileVal -> case moduFileVal of
        EdhString !moduFile -> exit moduFile
        _                   -> exit $ "<procedure: " <> procedureName pd <> ">"
 where
  !pd = edh'scope'proc scope
  !pb = edh'procedure'body $ edh'procedure'decl pd


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
  , edh'class'allocator :: !(ArgsPack -> EdhObjectAllocator)
    -- | the C3 linearized method resolution order, with self omitted
  , edh'class'mro :: !(TVar [Object])
  }
instance Eq Class where
  Class x'p _ _ _ == Class y'p _ _ _ = x'p == y'p
instance Hashable Class where
  hashWithSalt s (Class p _ _ _) = hashWithSalt s p

type EdhObjectAllocator = EdhAllocExit -> EdhTx
type EdhAllocExit = ObjectStore -> STM ()

edhClassName :: Object -> Text
edhClassName !clsObj = case edh'obj'store clsObj of
  ClassStore !cls -> procedureName $ edh'class'proc cls
  _               -> "<bogus-class>"

objClassName :: Object -> Text
objClassName = edhClassName . edh'obj'class


-- | An object views an entity, with inheritance relationship 
-- to any number of super objects.
data Object = Object {
    -- | unique identifier of an Edh object
    edh'obj'ident :: !Unique
    -- | the storage for entity attributes of the object
  , edh'obj'store :: !ObjectStore
    -- | the class object must have a 'ClassStore' storage
    -- note this field can not be strict, or it's infinite loop creating the
    -- meta class object (whose class is itself)
  , edh'obj'class :: Object
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
    ClassStore !cls ->
      "<object: " ++ T.unpack (procedureName $ edh'class'proc cls) ++ ">"
    _ -> "<bogus-object>"

data ObjectStore =
    HashStore !EntityStore
  | ClassStore !Class -- in case this is a class object
  | HostStore !Dynamic

-- | Try cast and unveil an Object's storage of a known type, while not
-- considering any super object eligible
castObjSelfStore :: forall a . (Typeable a) => Object -> STM (Maybe a)
castObjSelfStore !obj = case edh'obj'store obj of
  HostStore !hsd -> case fromDynamic hsd of
    Just (hsv :: a) -> return $ Just hsv
    Nothing         -> return Nothing
  _ -> return Nothing
-- | Try cast and unveil a possible Object's storage of a known type, while not
-- considering any super object eligible
castObjSelfStore' :: forall a . (Typeable a) => EdhValue -> STM (Maybe a)
castObjSelfStore' !val = case edhUltimate val of
  EdhObject !obj -> castObjSelfStore obj
  _              -> return Nothing

-- | Try cast and unveil an Object's storage of a known type
castObjectStore :: forall a . (Typeable a) => Object -> STM (Maybe (Object, a))
castObjectStore !obj = (obj :) <$> readTVar (edh'obj'supers obj) >>= goSearch
 where
  goSearch []         = return Nothing
  goSearch (o : rest) = castObjSelfStore o >>= \case
    Just !d -> return $ Just (o, d)
    Nothing -> goSearch rest

-- | Try cast and unveil a possible Object's storage of a known type
castObjectStore'
  :: forall a . (Typeable a) => EdhValue -> STM (Maybe (Object, a))
castObjectStore' !val = case edhUltimate val of
  EdhObject !obj -> castObjectStore obj
  _              -> return Nothing


-- | A world for Edh programs to change
data EdhWorld = EdhWorld {
    -- | root scope of this world
    edh'world'root :: !Scope
    -- | all operators declared in this world, this also used as the
    -- _world lock_ in parsing source code to be executed in this world
  , edh'world'operators :: !(TMVar OpPrecDict)
    -- | all modules loaded, being loaded, or failed loading into this world
  , edh'world'modules :: !(TMVar (Map.HashMap ModuleId (TVar ModuSlot)))
    -- | for console logging, input and output
  , edh'world'console :: !EdhConsole
    -- wrapping a scope as object for reflective purpose
  , edh'scope'wrapper :: !(Scope -> STM Object)
    -- wrapping a host exceptin as an Edh object
  , edh'exception'wrapper :: !(SomeException -> STM Object)
    -- create a new module object
  , edh'module'class :: !Object
  }
instance Eq EdhWorld where
  x == y =
    edh'scope'this (edh'world'root x) == edh'scope'this (edh'world'root y)

createNamespace :: EdhWorld -> Text -> [(AttrKey, EdhValue)] -> STM Object
createNamespace !world !nsName !nsArts = do
  !oidNs <- unsafeIOToSTM newUnique
  !hs    <- iopdFromList $ (AttrByName "__name__", EdhString nsName) : nsArts
  !ss    <- newTVar []
  let !nsObj = Object oidNs (HashStore hs) nsClass ss
  return nsObj
 where
  !rootScope = edh'world'root world
  !nsClass   = edh'obj'class $ edh'scope'this rootScope

type ModuleId = Text

data ModuSlot =
    ModuLoaded   !Object
  | ModuLoading  !Scope !(TVar [Object -> STM ()])
  | ModuFailed   !EdhValue

edhCreateModule :: EdhWorld -> Text -> ModuleId -> String -> STM Object
edhCreateModule !world !moduName !moduId !srcName = do
  !idModu <- unsafeIOToSTM newUnique
  !hs     <- iopdFromList
    [ (AttrByName "__name__", EdhString moduName)
    , (AttrByName "__path__", EdhString moduId)
    , (AttrByName "__file__", EdhString $ T.pack srcName)
    ]
  !ss <- newTVar []
  return Object { edh'obj'ident  = idModu
                , edh'obj'store  = HashStore hs
                , edh'obj'class  = edh'module'class world
                , edh'obj'supers = ss
                }

worldContext :: EdhWorld -> Context
worldContext !world = Context
  { edh'ctx'world        = world
  , edh'ctx'stack        = edh'world'root world :| []
  , edh'ctx'genr'caller  = Nothing
  , edh'ctx'match        = true
  , edh'ctx'stmt         = StmtSrc (startPosOfFile "<world>", VoidStmt)
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

-- | The task to be queued for execution of an Edh thread.
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
  !(TVar Bool -> EdhTx)
data DeferRecord = DeferRecord
  -- | origin ets upon the deferred action is scheduled
  !EdhThreadState
  -- | deferred action to be performed upon termination of the target Edh
  -- thread
  !(EdhThreadState -> STM ())


-- | Perform a subsquent STM action within an Edh thread, honoring 
-- @edh'in'tx ets@ in deciding whether to do it in current STM transaction, or
-- to do it in a separate, later STM transaction, which is scheduled by putting
-- the action into the Edh thread's task queue.
--
-- @edh'in'tx ets@ is normally controlled by the `ai` keyword at scripting
-- level, this implements the semantics of it
edhDoSTM :: EdhThreadState -> STM () -> STM ()
edhDoSTM !ets !act = if edh'in'tx ets
  then act
  else writeTBQueue (edh'task'queue ets) $ EdhDoSTM ets act
{-# INLINE edhDoSTM #-}


-- | Composable transactional computation, to be performed in an Edh thread.
--
-- Note such an computation can write subsequent STM actions into the task
--      queue of the thread state, so as to schedule some more computation
--      to be performed in subsequent, separate STM transactions
--
-- this is somewhat similar to @ 'ReaderT' 'EdhThreadState' 'STM' @, but not
-- monadic
type EdhTx = EdhThreadState -> STM ()

-- | The commonplace type of CPS exit for transactional Edh computations
type EdhTxExit = EdhValue -> EdhTx

endOfEdh :: EdhTxExit
endOfEdh _ _ = return ()
{-# INLINE endOfEdh #-}

-- | Schedule forking of a GHC thread to bootstrap an Edh thread to run the
-- specified Edh computation, with the specified thread state modifer applied
-- before the computation is stated in the descendant thread.
--
-- NOTE this happens as part of current STM tx, the actual fork won't happen if
--      any subsequent Edh code within the tx throws without recovered
forkEdh :: (EdhThreadState -> EdhThreadState) -> EdhTx -> EdhTxExit -> EdhTx
forkEdh !bootMod !p !exit !etsForker = do
  writeTBQueue (edh'fork'queue etsForker) (etsForker, p . bootMod)
  exitEdh etsForker exit nil
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
edhContSTM :: STM () -> EdhTx
edhContSTM !actSTM !ets =
  writeTBQueue (edh'task'queue ets) $ EdhDoSTM ets actSTM
{-# INLINE edhContSTM #-}

-- | Schedule an IO action to be performed in current Edh thread, but after
-- current STM tx committed, and after some txs, those possibly already
-- scheduled.
--
-- NOTE this happens as part of current STM tx, so the actual action won't be
--      scheduled if any subsequent Edh code within the tx throws without
--      recovered
-- CAVEAT pay special attention in using this, to not break the semantics of
--       `ai` keyword at scripting level
edhContIO :: IO () -> EdhTx
edhContIO !actIO !ets = writeTBQueue (edh'task'queue ets) $ EdhDoIO ets actIO
{-# INLINE edhContIO #-}

-- | Start the specified Edh computation for running in current Edh thread with
-- the specified state.
runEdhTx :: EdhThreadState -> EdhTx -> STM ()
runEdhTx !ets !p = p ets
{-# INLINE runEdhTx #-}

-- | Augment the specified Edh computation, to run in the specified state,
-- regardless of whatever previous state the thread has.
edhSwitchState :: EdhThreadState -> EdhTx -> EdhTx
edhSwitchState !ets !etx = const $ edhDoSTM ets $ etx ets
{-# INLINE edhSwitchState #-}

-- | Exit an Edh computation in CPS.
--
-- @edh'in'tx ets@ is normally controlled by the `ai` keyword at scripting
-- level, this implements the semantics of it
exitEdhTx :: EdhTxExit -> EdhValue -> EdhTx
exitEdhTx !exit !val !ets = edhDoSTM ets $ exit val ets
{-# INLINE exitEdhTx #-}

-- | Exit an Edh computation from STM monad in CPS.
--
-- @edh'in'tx ets@ is normally controlled by the `ai` keyword at scripting
-- level, this implements the semantics of it
exitEdh :: EdhThreadState -> EdhTxExit -> EdhValue -> STM ()
exitEdh !ets !exit !val = edhDoSTM ets $ exit val ets
{-# INLINE exitEdh #-}


-- | Type of an intrinsic infix operator in the host language (Haskell).
--
-- Note no stack frame is created/pushed when an intrinsic operator is called.
type EdhIntrinsicOp = Expr -> Expr -> EdhTxExit -> EdhTx

edhFlipOp :: EdhIntrinsicOp -> EdhIntrinsicOp
edhFlipOp !op = flipped
 where
  flipped :: EdhIntrinsicOp
  flipped !lhExpr !rhExpr !exit = op rhExpr lhExpr exit

data IntrinOpDefi = IntrinOpDefi {
    intrinsic'op'uniq :: !Unique
  , intrinsic'op'symbol :: !AttrName
  , intrinsic'op :: EdhIntrinsicOp
  }


-- | Monotype for the last part of an 'EdhCallable' procedure
type EdhHostProc -- such a procedure servs as the callee
  =  EdhTxExit -- ^ the CPS exit to return a value from this procedure
  -> EdhTx


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
launchEventProducer :: EdhTxExit -> EventSink -> EdhTx -> EdhTx
launchEventProducer !exit sink@(EventSink _ _ _ _ !subc) !producerTx !etsConsumer
  = do
    subcBefore <- readTVar subc
    let prodThAct !etsProducer = do
          subcNow <- readTVar subc
          when (subcNow == subcBefore) retry
          producerTx etsProducer
    runEdhTx etsConsumer
      $ forkEdh id prodThAct
      $ const
      $ exitEdhTx exit
      $ EdhSink sink


-- | executable precedures
data EdhProc =
    EdhIntrOp !Precedence !IntrinOpDefi
  | EdhOprtor !Precedence !(Maybe EdhValue) !ProcDefi
  | EdhMethod !ProcDefi
  | EdhGnrtor !ProcDefi
  | EdhIntrpr !ProcDefi
  | EdhPrducr !ProcDefi
  -- similar to Python Descriptor
  -- with a getter method and optionally a settor method, for properties
  -- (programmatically managed attributes) to be defined on objects
  -- deleter semantic is expressed as calling setter without arg
  | EdhDescriptor !ProcDefi !(Maybe ProcDefi)

instance Show EdhProc where
  show (EdhIntrOp !preced (IntrinOpDefi _ !opSym _)) =
    "intrinsic: (" ++ T.unpack opSym ++ ") " ++ show preced
  show (EdhOprtor !preced _ !pd) =
    "operator: (" ++ T.unpack (procedureName pd) ++ ") " ++ show preced
  show (EdhMethod !pd) = T.unpack ("method: " <> procedureName pd)
  show (EdhGnrtor !pd) = T.unpack ("generator: " <> procedureName pd)
  show (EdhIntrpr !pd) = T.unpack ("interpreter: " <> procedureName pd)
  show (EdhPrducr !pd) = T.unpack ("producer: " <> procedureName pd)

  show (EdhDescriptor !getter !setter) =
    (<> T.unpack (procedureName getter) <> ">") $ case setter of
      Nothing -> "readonly property "
      Just _  -> "property "

instance Eq EdhProc where
  EdhIntrOp _ (IntrinOpDefi x'u _ _) == EdhIntrOp _ (IntrinOpDefi y'u _ _) =
    x'u == y'u
  EdhOprtor _ _ x == EdhOprtor _ _ y = x == y
  EdhMethod x     == EdhMethod y     = x == y
  EdhGnrtor x     == EdhGnrtor y     = x == y
  EdhIntrpr x     == EdhIntrpr y     = x == y
  EdhPrducr x     == EdhPrducr y     = x == y

  EdhDescriptor x'getter x'setter == EdhDescriptor y'getter y'setter =
    x'getter == y'getter && x'setter == y'setter

  _ == _ = False

instance Hashable EdhProc where
  hashWithSalt s (EdhIntrOp _ (IntrinOpDefi x'u _ _)) = hashWithSalt s x'u
  hashWithSalt s (EdhMethod x                       ) = hashWithSalt s x
  hashWithSalt s (EdhOprtor _ _ x                   ) = hashWithSalt s x
  hashWithSalt s (EdhGnrtor x                       ) = hashWithSalt s x
  hashWithSalt s (EdhIntrpr x                       ) = hashWithSalt s x
  hashWithSalt s (EdhPrducr x                       ) = hashWithSalt s x

  hashWithSalt s (EdhDescriptor getter setter) =
    s `hashWithSalt` getter `hashWithSalt` setter

callableName :: EdhProc -> Text
callableName = \case
  EdhIntrOp _preced (IntrinOpDefi _ !opSym _) -> "(" <> opSym <> ")"
  EdhOprtor _preced _ !pd                     -> "(" <> procedureName pd <> ")"
  EdhMethod !pd                               -> procedureName pd
  EdhGnrtor !pd                               -> procedureName pd
  EdhIntrpr !pd                               -> procedureName pd
  EdhPrducr !pd                               -> procedureName pd
  EdhDescriptor !getter !setter ->
    (<> procedureName getter <> ">") $ case setter of
      Nothing -> "<readonly property "
      Just _  -> "<property "

callableDoc :: EdhProc -> Maybe DocComment
callableDoc = \case
  EdhIntrOp _preced _                -> Nothing
  EdhOprtor _preced _ !pd            -> edh'procedure'doc pd
  EdhMethod !pd                      -> edh'procedure'doc pd
  EdhGnrtor !pd                      -> edh'procedure'doc pd
  EdhIntrpr !pd                      -> edh'procedure'doc pd
  EdhPrducr !pd                      -> edh'procedure'doc pd
  EdhDescriptor !getter !maybeSetter -> case maybeSetter of
    Nothing     -> edh'procedure'doc getter
    Just setter -> edh'procedure'doc setter


-- Atop Haskell, most types in Edh the surface language, are for
-- immutable values, besides dict and list, the only other mutable
-- data structure in Edh, is 'EntityStore', an **entity** is a set
-- of mutable attributes.
--
-- After applied a set of rules/constraints about how attributes
-- of an entity can be retrived and altered, it becomes an object,
-- while a class is just an object with a little more special
-- semantics.
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
  -- wraps some host data dynamically mutable, while a class object as a
  -- special case, can construct other objects being its instances, and
  -- the class object's entity attributes are shared by those instances as
  -- static attributes
  | EdhObject !Object

  -- | a callable procedure
  -- with the effect outer stack if resolved as an effectful artifact
  | EdhProcedure !EdhProc !(Maybe [Scope])
  -- | a callable procedure bound to a specific this object and that object
  -- with the effect outer stack if resolved as an effectful artifact
  | EdhBoundProc !EdhProc !Object !Object !(Maybe [Scope])

  -- * flow control
  | EdhBreak
  | EdhContinue
  | EdhCaseClose !EdhValue
  | EdhCaseOther
  | EdhFallthrough
  | EdhRethrow
  | EdhYield !EdhValue
  | EdhReturn !EdhValue

  | EdhOrd !Ordering

  -- | prefer better efforted result, but can default to the specified expr
  -- if there's no better result applicable
  -- 
  -- similar to NotImplemented as in Python, this is used to signal
  -- try-next-impl semantics:
  --
  -- - @default { throw xxx }@ can be used to signal that it has to have
  --   some more concrete implementation
  --
  -- - @NA := default nil@ can be used to prefer an even more deferred default
  --   if any exists, then an all-nil default chain will finally result in
  --   @nil@, i.e. non-exist
  | EdhDefault !Unique !Expr !(Maybe EdhThreadState)

  -- | event sink
  | EdhSink !EventSink

  -- | named value, a.k.a. term definition
  | EdhNamedValue !AttrName !EdhValue

  -- | reflective expr, with source (or not, if empty)
  | EdhExpr !Unique !Expr !Text

instance Show EdhValue where
  show (EdhType t)              = show t
  show EdhNil                   = "nil"
  show (EdhDecimal v          ) = showDecimal v
  show (EdhBool    v          ) = if v then "true" else "false"
  show (EdhBlob    b          ) = "<blob#" <> show (B.length b) <> ">"
  show (EdhString  v          ) = show v
  show (EdhSymbol  v          ) = show v
  show (EdhUUID    v          ) = "UUID('" <> UUID.toString v <> "')"

  show (EdhPair k v           ) = show k <> ":" <> show v
  show (EdhArgsPack v         ) = show v

  show (EdhDict     v         ) = show v
  show (EdhList     v         ) = show v

  show (EdhObject   v         ) = show v

  show (EdhProcedure !pc _    ) = "<callable:" ++ show pc ++ ">"
  show (EdhBoundProc !pc _ _ _) = "<bound:" ++ show pc ++ ">"

  show EdhBreak                 = "<break>"
  show EdhContinue              = "<continue>"
  show (EdhCaseClose v)         = "<caseclose: " ++ show v ++ ">"
  show EdhCaseOther             = "<caseother>"
  show EdhFallthrough           = "<fallthrough>"
  show EdhRethrow               = "<rethrow>"
  show (EdhYield  v     )       = "<yield: " ++ show v ++ ">"
  show (EdhReturn v     )       = "<return: " ++ show v ++ ">"

  show (EdhOrd    ord   )       = show ord

  show (EdhDefault _ x _)       = case x of
    ExprWithSrc _ [SrcSeg src] -> "default " <> T.unpack src
    _                          -> "<default: " ++ show x ++ ">"

  show (EdhSink v) = show v

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
  EdhType x        == EdhType y        = x == y
  EdhNil           == EdhNil           = True
  EdhDecimal x     == EdhDecimal y     = x == y
  EdhBool    x     == EdhBool    y     = x == y
  EdhBlob    x     == EdhBlob    y     = x == y
  EdhString  x     == EdhString  y     = x == y
  EdhSymbol  x     == EdhSymbol  y     = x == y
  EdhUUID    x     == EdhUUID    y     = x == y

  EdhPair x'k x'v  == EdhPair y'k y'v  = x'k == y'k && x'v == y'v
  EdhArgsPack x    == EdhArgsPack y    = x == y

  EdhDict     x    == EdhDict     y    = x == y
  EdhList     x    == EdhList     y    = x == y

  EdhObject   x    == EdhObject   y    = x == y

  EdhProcedure x _ == EdhProcedure y _ = x == y
  EdhBoundProc x x'this x'that _ == EdhBoundProc y y'this y'that _ =
    x == y && x'this == y'this && x'that == y'that


  EdhBreak                    == EdhBreak                    = True
  EdhContinue                 == EdhContinue                 = True
  EdhCaseClose x              == EdhCaseClose y              = x == y
  EdhCaseOther                == EdhCaseOther                = True
  EdhFallthrough              == EdhFallthrough              = True
  EdhRethrow                  == EdhRethrow                  = True
-- todo: regard a yielded/returned value equal to the value itself ?
  EdhYield  x'v               == EdhYield  y'v               = x'v == y'v
  EdhReturn x'v               == EdhReturn y'v               = x'v == y'v

  EdhOrd    x                 == EdhOrd    y                 = x == y

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
  hashWithSalt s (EdhType x)        = hashWithSalt s $ 1 + fromEnum x
  hashWithSalt s EdhNil             = hashWithSalt s (0 :: Int)
  hashWithSalt s (EdhDecimal x    ) = hashWithSalt s x
  hashWithSalt s (EdhBool    x    ) = hashWithSalt s x
  hashWithSalt s (EdhBlob    x    ) = hashWithSalt s x
  hashWithSalt s (EdhString  x    ) = hashWithSalt s x
  hashWithSalt s (EdhSymbol  x    ) = hashWithSalt s x
  hashWithSalt s (EdhUUID    x    ) = hashWithSalt s x

  hashWithSalt s (EdhPair k v     ) = s `hashWithSalt` k `hashWithSalt` v
  hashWithSalt s (EdhArgsPack x   ) = hashWithSalt s x

  hashWithSalt s (EdhDict     x   ) = hashWithSalt s x
  hashWithSalt s (EdhList     x   ) = hashWithSalt s x

  hashWithSalt s (EdhObject   x   ) = hashWithSalt s x

  hashWithSalt s (EdhProcedure x _) = hashWithSalt s x
  hashWithSalt s (EdhBoundProc x this that _) =
    s `hashWithSalt` x `hashWithSalt` this `hashWithSalt` that

  hashWithSalt s EdhBreak    = hashWithSalt s (-1 :: Int)
  hashWithSalt s EdhContinue = hashWithSalt s (-2 :: Int)
  hashWithSalt s (EdhCaseClose v) =
    s `hashWithSalt` (-3 :: Int) `hashWithSalt` v
  hashWithSalt s EdhCaseOther   = hashWithSalt s (-4 :: Int)
  hashWithSalt s EdhFallthrough = hashWithSalt s (-5 :: Int)
  hashWithSalt s EdhRethrow     = hashWithSalt s (-6 :: Int)
  hashWithSalt s (EdhYield  v)  = s `hashWithSalt` (-7 :: Int) `hashWithSalt` v
  hashWithSalt s (EdhReturn v)  = s `hashWithSalt` (-8 :: Int) `hashWithSalt` v

  hashWithSalt s (EdhOrd    o)  = s `hashWithSalt` (-10 :: Int) `hashWithSalt` o

  hashWithSalt s (EdhDefault u _ _) =
    s `hashWithSalt` (-9 :: Int) `hashWithSalt` u

  hashWithSalt s (EdhSink x              ) = hashWithSalt s x

  hashWithSalt s (EdhNamedValue _ v      ) = hashWithSalt s v

  hashWithSalt s (EdhExpr _ (LitExpr l) _) = hashWithSalt s l
  hashWithSalt s (EdhExpr u _           _) = hashWithSalt s u


edhDeCaseClose :: EdhValue -> EdhValue
edhDeCaseClose (EdhCaseClose !val) = edhDeCaseClose val
edhDeCaseClose !val                = val

edhDeCaseWrap :: EdhValue -> EdhValue
edhDeCaseWrap (EdhCaseClose !val) = edhDeCaseWrap val
edhDeCaseWrap EdhCaseOther        = nil
edhDeCaseWrap EdhFallthrough      = nil
edhDeCaseWrap !val                = val

edhUltimate :: EdhValue -> EdhValue
edhUltimate (EdhNamedValue _ !v) = edhUltimate v
edhUltimate (EdhReturn !v      ) = edhUltimate v
edhUltimate (EdhYield  !v      ) = edhUltimate v
edhUltimate !v                   = edhDeCaseWrap v


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

-- | NA for not-applicable, similar to @NotImplemented@ as in Python
edhNA :: EdhValue
edhNA = EdhNamedValue "NA" $ EdhDefault
  (unsafePerformIO newUnique)
  (ExprWithSrc (LitExpr NilLiteral) [SrcSeg "nil"])
  Nothing
{-# NOINLINE edhNA #-}


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


data SourceSpan = SourceSpan {
  source'span'start :: {-# UNPACK #-} !SourcePos
  , source'span'end'line :: {-# UNPACK #-} !Pos
  , source'span'end'column :: {-# UNPACK #-} !Pos
  }
instance Eq SourceSpan where
  (SourceSpan x'start x'end'line x'end'col) == (SourceSpan y'start y'end'line y'end'col)
    = x'start == y'start && x'end'line == y'end'line && x'end'col == y'end'col
startPosOfFile :: FilePath -> SourceSpan
startPosOfFile !n = SourceSpan (initialPos n) pos1 pos1
prettySourceLoc :: SourceSpan -> String
prettySourceLoc (SourceSpan !start _ _) = sourcePosPretty start


newtype StmtSrc = StmtSrc (SourceSpan, Stmt)
instance Eq StmtSrc where
  StmtSrc (x'sp, _) == StmtSrc (y'sp, _) = x'sp == y'sp
instance Show StmtSrc where
  show (StmtSrc (_sp, stmt)) = show stmt

type DocComment = [Text]


data Stmt =
      -- | literal `pass` to fill a place where a statement needed,
      -- same as in Python
      VoidStmt
      -- | similar to `go` in Go, starts goroutine
    | GoStmt !Expr
      -- | not similar to `defer` in Go (in Go `defer` snapshots arg values
      -- and schedules execution on func return), but in Edh `defer`
      -- schedules execution on thread termination
    | DeferStmt !Expr
      -- | artifacts introduced within an `effect` statement will be put
      -- into effect namespace, which as currently implemented, a dict
      -- resides in current scope entity addressed by name `__exports__`
    | EffectStmt !Expr !(Maybe DocComment)
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
    | PerceiveStmt !Expr !StmtSrc
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
    | ExprStmt !Expr !(Maybe DocComment)
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
  show = T.unpack . attrAddrStr
instance Hashable AttrAddressor where
  hashWithSalt s (NamedAttr name) = s `hashWithSalt` name
  hashWithSalt s (SymbolicAttr sym) =
    s `hashWithSalt` ("@" :: Text) `hashWithSalt` sym

attrAddrStr :: AttrAddressor -> Text
attrAddrStr (NamedAttr    n) = n
attrAddrStr (SymbolicAttr s) = "@" <> s


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
  , edh'procedure'body :: !(Either StmtSrc (ArgsPack -> EdhHostProc))
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
  , edh'procedure'doc :: Maybe DocComment
  , edh'procedure'decl :: {-# UNPACK #-} !ProcDecl
  }
instance Eq ProcDefi where
  ProcDefi x'u _ _ _ _ == ProcDefi y'u _ _ _ _ = x'u == y'u
instance Ord ProcDefi where
  compare (ProcDefi x'u _ _ _ _) (ProcDefi y'u _ _ _ _) = compare x'u y'u
instance Hashable ProcDefi where
  hashWithSalt s (ProcDefi u _ _ _ _) = s `hashWithSalt` u
instance Show ProcDefi where
  show (ProcDefi _ !name _ _ (ProcDecl !addr _ !pb)) = case pb of
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

data Expr =
    -- | the expr will be evaluated with result discarded,
    -- should always result in nil
    VoidExpr !Expr

    -- | atomically isolated, mark an expression to be evaluated in a single
    -- STM transaction as a whole
  | AtoIsoExpr !Expr

  | LitExpr !Literal
  | PrefixExpr !Prefix !Expr

  | IfExpr { if'condition :: !Expr
          , if'consequence :: !StmtSrc
          , if'alternative :: !(Maybe StmtSrc)
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
    -- | namespace definition
  | NamespaceExpr !ProcDecl !ArgsPacker
    -- | class definition
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

  | BlockExpr ![StmtSrc]
  | ScopedBlockExpr ![StmtSrc]

  | YieldExpr !Expr

  -- | a for-from-do loop is made an expression in Edh, so it can
  -- appear as the right-hand expr of the comprehension (=<) operator.
  | ForExpr !ArgsReceiver !Expr !StmtSrc

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
  deriving (Eq, Show)

data SourceSeg = SrcSeg !Text | IntplSeg !Expr
  deriving (Eq, Show)

data Literal =
    SinkCtor
  | NilLiteral
  | DecLiteral !Decimal
  | BoolLiteral !Bool
  | StringLiteral !Text
  | TypeLiteral !EdhTypeValue
  | ValueLiteral !EdhValue
  deriving (Eq, Show)
instance Hashable Literal where
  hashWithSalt s SinkCtor          = hashWithSalt s (-1 :: Int)
  hashWithSalt s NilLiteral        = hashWithSalt s (0 :: Int)
  hashWithSalt s (DecLiteral    x) = hashWithSalt s x
  hashWithSalt s (BoolLiteral   x) = hashWithSalt s x
  hashWithSalt s (StringLiteral x) = hashWithSalt s x
  hashWithSalt s (TypeLiteral   x) = hashWithSalt s x
  hashWithSalt s (ValueLiteral  x) = hashWithSalt s x


-- | the type for the value of type of a value
-- note nil has no type, its type if you really ask, is nil
data EdhTypeValue =
    TypeType
  | DecimalType
  | BoolType
  | StringType
  | BlobType
  | SymbolType
  | UUIDType
  | ObjectType
  | ClassType
  | HostClassType
  | DictType
  | ListType
  | PairType
  | ArgsPackType
  | BlockType
  | HostMethodType
  | HostOperType
  | HostGenrType
  | IntrinsicType
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
  | OrdType
  | DefaultType
  | SinkType
  | ExprType
  deriving (Enum, Eq, Ord, Show)
instance Hashable EdhTypeValue where
  hashWithSalt s t = hashWithSalt s $ fromEnum t

edhTypeNameOf :: EdhValue -> String
edhTypeNameOf EdhNil               = "nil"
edhTypeNameOf (EdhNamedValue _n v) = edhTypeNameOf v
edhTypeNameOf v                    = show $ edhTypeOf v

-- | Get the type tag of an value
--
-- Passing in a `nil` value will hit bottom (crash the process) here,
-- use `edhTypeNameOf` if all you want is a type name shown to user.
edhTypeOf :: EdhValue -> EdhTypeValue

-- it's a taboo to get the type of a nil, either named or not
edhTypeOf EdhNil        = undefined

edhTypeOf EdhType{}     = TypeType

edhTypeOf EdhDecimal{}  = DecimalType
edhTypeOf EdhBool{}     = BoolType
edhTypeOf EdhBlob{}     = BlobType
edhTypeOf EdhString{}   = StringType
edhTypeOf EdhSymbol{}   = SymbolType
edhTypeOf EdhUUID{}     = UUIDType

edhTypeOf EdhPair{}     = PairType
edhTypeOf EdhArgsPack{} = ArgsPackType

edhTypeOf EdhDict{}     = DictType
edhTypeOf EdhList{}     = ListType

edhTypeOf (EdhObject o) = case edh'obj'store o of
  HashStore{} -> ObjectType
  ClassStore !cls ->
    case edh'procedure'body $ edh'procedure'decl $ edh'class'proc cls of
      Left{}  -> ClassType
      Right{} -> HostClassType
  HostStore{} -> ObjectType -- TODO add a @HostObjectType@ to distinguish?

edhTypeOf (EdhProcedure pc _    ) = edhProcTypeOf pc
edhTypeOf (EdhBoundProc pc _ _ _) = edhProcTypeOf pc

edhTypeOf EdhBreak                = BreakType
edhTypeOf EdhContinue             = ContinueType
edhTypeOf EdhCaseClose{}          = CaseCloseType
edhTypeOf EdhCaseOther            = CaseOtherType
edhTypeOf EdhFallthrough          = FallthroughType
edhTypeOf EdhRethrow              = RethrowType
edhTypeOf EdhYield{}              = YieldType
edhTypeOf EdhReturn{}             = ReturnType
edhTypeOf EdhOrd{}                = OrdType
edhTypeOf EdhDefault{}            = DefaultType
edhTypeOf EdhSink{}               = SinkType
edhTypeOf (EdhNamedValue _ v)     = edhTypeOf v
edhTypeOf EdhExpr{}               = ExprType

edhProcTypeOf :: EdhProc -> EdhTypeValue
edhProcTypeOf = \case
  EdhIntrOp{} -> IntrinsicType
  EdhOprtor _ _ (ProcDefi _ _ _ _ (ProcDecl _ _ pb)) -> case pb of
    Left  _ -> OperatorType
    Right _ -> HostOperType
  EdhMethod (ProcDefi _ _ _ _ (ProcDecl _ _ pb)) -> case pb of
    Left  _ -> MethodType
    Right _ -> HostMethodType
  EdhGnrtor (ProcDefi _ _ _ _ (ProcDecl _ _ pb)) -> case pb of
    Left  _ -> GeneratorType
    Right _ -> HostGenrType
  EdhIntrpr{}     -> InterpreterType
  EdhPrducr{}     -> ProducerType
  EdhDescriptor{} -> DescriptorType


objectScope :: Object -> STM Scope
objectScope !obj = case edh'obj'store obj of

  HostStore _ -> do
    -- provide the scope for a host object with an ad-hoc empty hash entity
    !hs <- iopdEmpty
    return Scope
      { edh'scope'entity  = hs
      , edh'scope'this    = obj
      , edh'scope'that    = obj
      , edh'excpt'hndlr   = defaultEdhExcptHndlr
      , edh'scope'proc    = ocProc
      , edh'scope'caller  = StmtSrc
                              (startPosOfFile "<host-object-scope>", VoidStmt)
      , edh'effects'stack = []
      }

  ClassStore (Class !cp !cs _ _) -> return Scope
    { edh'scope'entity  = cs
    , edh'scope'this    = obj
    , edh'scope'that    = obj
    , edh'excpt'hndlr   = defaultEdhExcptHndlr
    , edh'scope'proc    = cp
    , edh'scope'caller  = StmtSrc (startPosOfFile "<class-scope>", VoidStmt)
    , edh'effects'stack = []
    }

  HashStore !hs ->
    let mustStr !v = case edhUltimate v of
          EdhString !s -> s
          _            -> error $ "bug: not a string - " <> show v
    in
      case procedureName ocProc of
        "module" -> do
          !moduPath <-
            mustStr
              <$> iopdLookupDefault (EdhString "<anonymous>")
                                    (AttrByName "__path__")
                                    hs
          !moduFile <-
            mustStr
              <$> iopdLookupDefault (EdhString "<on-the-fly>")
                                    (AttrByName "__file__")
                                    hs
          return Scope
            { edh'scope'entity  = hs
            , edh'scope'this    = obj
            , edh'scope'that    = obj
            , edh'excpt'hndlr   = defaultEdhExcptHndlr
            , edh'scope'proc    = ProcDefi
              { edh'procedure'ident = edh'obj'ident obj
              , edh'procedure'name  = AttrByName moduPath
              , edh'procedure'lexi  = edh'procedure'lexi ocProc
              , edh'procedure'doc   = Nothing
              , edh'procedure'decl  = ProcDecl
                { edh'procedure'addr = NamedAttr moduPath
                , edh'procedure'args = PackReceiver []
                , edh'procedure'body = Left
                  $ StmtSrc (startPosOfFile $ T.unpack moduFile, VoidStmt)
                }
              }
            , edh'scope'caller  = StmtSrc (startPosOfFile "<run-edh>", VoidStmt)
            , edh'effects'stack = []
            }
        _ -> return Scope
          { edh'scope'entity  = hs
          , edh'scope'this    = obj
          , edh'scope'that    = obj
          , edh'excpt'hndlr   = defaultEdhExcptHndlr
          , edh'scope'proc    = ocProc
          , edh'scope'caller  = StmtSrc
                                  (startPosOfFile "<object-scope>", VoidStmt)
          , edh'effects'stack = []
          }
 where
  !oc = case edh'obj'store $ edh'obj'class obj of
    ClassStore !cls -> cls
    _               -> error "bug: class of an object not bearing ClassStore"
  ocProc = edh'class'proc oc


-- | Create a reflective object capturing the specified scope as from the
-- specified context
--
-- todo currently only lexical context is recorded, the call frames may
--      be needed in the future
mkScopeWrapper :: Context -> Scope -> STM Object
mkScopeWrapper !ctx !scope = edhWrapScope scope
  where edhWrapScope = edh'scope'wrapper $ edh'ctx'world ctx


data EdhIndex = EdhIndex !Int | EdhAny | EdhAll | EdhSlice {
    edh'slice'start :: !(Maybe Int)
  , edh'slice'stop :: !(Maybe Int)
  , edh'slice'step :: !(Maybe Int)
  } deriving (Eq)


mkHostProc
  :: Scope
  -> (ProcDefi -> EdhProc)
  -> AttrName
  -> (ArgsPack -> EdhHostProc, ArgsReceiver)
  -> STM EdhValue
mkHostProc !scope !vc !nm (!p, !args) = do
  !u <- unsafeIOToSTM newUnique
  return $ EdhProcedure
    (vc ProcDefi
      { edh'procedure'ident = u
      , edh'procedure'name  = AttrByName nm
      , edh'procedure'lexi  = scope
      , edh'procedure'doc   = Nothing
      , edh'procedure'decl  = ProcDecl { edh'procedure'addr = NamedAttr nm
                                       , edh'procedure'args = args
                                       , edh'procedure'body = Right p
                                       }
      }
    )
    Nothing

mkSymbolicHostProc
  :: Scope
  -> (ProcDefi -> EdhProc)
  -> Symbol
  -> (ArgsPack -> EdhHostProc, ArgsReceiver)
  -> STM EdhValue
mkSymbolicHostProc !scope !vc !sym (!p, !args) = do
  !u <- unsafeIOToSTM newUnique
  return $ EdhProcedure
    (vc ProcDefi
      { edh'procedure'ident = u
      , edh'procedure'name  = AttrBySym sym
      , edh'procedure'lexi  = scope
      , edh'procedure'doc   = Nothing
      , edh'procedure'decl  = ProcDecl
                                { edh'procedure'addr = SymbolicAttr
                                                         $ symbolName sym
                                , edh'procedure'args = args
                                , edh'procedure'body = Right p
                                }
      }
    )
    Nothing

