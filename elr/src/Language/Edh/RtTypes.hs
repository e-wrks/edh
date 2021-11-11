module Language.Edh.RtTypes where

-- import           Debug.Trace

import Control.Applicative
import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception (SomeException)
import Control.Monad
import qualified Data.Bits as Bits
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import Data.Dynamic
import qualified Data.HashMap.Strict as Map
import Data.Hashable (Hashable (hashWithSalt))
import Data.IORef
import Data.List
import Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.UUID as UUID
import qualified Data.UUID.V4 as UUID
import Data.Unique
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Control
import Language.Edh.IOPD
import System.IO.Unsafe (unsafePerformIO)
import System.Posix
import Prelude

-- | A pack of evaluated argument values with positional/keyword origin,
-- this works in places of tuples in other languages, apk in Edh can be
-- considered a tuple if only positional arguments inside.
-- Specifically, an empty apk is just considered an empty tuple.
data ArgsPack = ArgsPack
  { positional'args :: ![EdhValue],
    keyword'args :: !KwArgs
  }
  deriving (Eq)

type KwArgs = OrderedDict AttrKey EdhValue

instance Hashable ArgsPack where
  hashWithSalt s (ArgsPack !args !kwargs) =
    s `hashWithSalt` args `hashWithSalt` kwargs

instance Show ArgsPack where
  show (ArgsPack !args kwargs) =
    if null args && odNull kwargs
      then "()"
      else
        "( "
          ++ concat [show p ++ ", " | p <- args]
          ++ concat
            [show kw ++ "=" ++ show v ++ ", " | (kw, v) <- odToList kwargs]
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

type DictStore = IOPD EdhValue EdhValue

-- | Create a new Edh dict from a list of entries
--
-- Note nil allowed as valid key, nil value triggers deletion semantics
createEdhDict :: [(EdhValue, EdhValue)] -> STM Dict
createEdhDict !entries = do
  !u <- unsafeIOToSTM newUnique
  Dict u <$> iopdFromList' edhValueIdent entries

-- | Set one dict item value by key
--
-- Note nil allowed as valid key, nil value triggers deletion semantics
setDictItem :: EdhValue -> EdhValue -> DictStore -> STM ()
setDictItem = iopdInsert' edhValueIdent

lookupDictItem :: EdhValue -> DictStore -> STM (Maybe EdhValue)
lookupDictItem = iopdLookup' edhValueIdent

dictEntryList :: DictStore -> STM [EdhValue]
dictEntryList !d =
  (<$> iopdToList d) $ fmap $ \(k, v) -> EdhArgsPack $ ArgsPack [k, v] odEmpty

-- | Identity value of an arbitrary value
--
-- this follows the semantic of Python's `id` function for object values and
-- a few other types, notably including event sink values;
-- and for values of immutable types, this follows the semantic of Haskell to
-- just return the value itself.
--
-- but unlike Python's `id` function which returns integers, here we return
-- `UUID`s for objects et al.
edhValueIdent :: EdhValue -> STM EdhValue
edhValueIdent = identityOf
  where
    idFromUnique :: Unique -> EdhValue
    idFromUnique !u =
      EdhUUID $
        UUID.fromWords
          0xcafe
          0xface
          (fromIntegral $ Bits.shiftR i 32)
          (fromIntegral i)
      where
        -- todo hashUnique doesn't guarantee free of collision, better impl?
        i = hashUnique u

    identityOf :: EdhValue -> STM EdhValue
    identityOf (EdhObject !o) = idOfObj o
    identityOf (EdhSink !s) = return $ idFromUnique $ sink'uniq s
    identityOf (EdhNamedValue !n !v) = EdhNamedValue n <$> identityOf v
    identityOf (EdhRange (ClosedBound !l) (ClosedBound !u)) = do
      l'i <- identityOf l
      u'i <- identityOf u
      return $ EdhRange (ClosedBound l'i) (ClosedBound u'i)
    identityOf (EdhRange (ClosedBound !l) (OpenBound !u)) = do
      l'i <- identityOf l
      u'i <- identityOf u
      return $ EdhRange (ClosedBound l'i) (OpenBound u'i)
    identityOf (EdhRange (OpenBound !l) (ClosedBound !u)) = do
      l'i <- identityOf l
      u'i <- identityOf u
      return $ EdhRange (OpenBound l'i) (ClosedBound u'i)
    identityOf (EdhRange (OpenBound !l) (OpenBound !u)) = do
      l'i <- identityOf l
      u'i <- identityOf u
      return $ EdhRange (OpenBound l'i) (OpenBound u'i)
    identityOf (EdhPair !l !r) = liftA2 EdhPair (identityOf l) (identityOf r)
    identityOf (EdhDict (Dict !u _)) = return $ idFromUnique u
    identityOf (EdhList (List !u _)) = return $ idFromUnique u
    identityOf (EdhProcedure !p _) = return $ idOfProc p
    identityOf (EdhBoundProc !p !this !that _) =
      EdhPair (idOfProc p) <$> liftA2 EdhPair (idOfObj this) (idOfObj that)
    identityOf (EdhExpr (ExprDefi !u _ _) _) = return $ idFromUnique u
    identityOf (EdhArgsPack (ArgsPack !args !kwargs)) =
      EdhArgsPack
        <$> liftA2
          ArgsPack
          (sequence $ identityOf <$> args)
          (odMapSTM identityOf kwargs)
    identityOf !v = return v

    idOfObj :: Object -> STM EdhValue
    idOfObj o = case edh'obj'store o of
      HashStore !hs ->
        iopdLookup (AttrByName "__id__") hs >>= \case
          Just !idv -> identityOf idv
          _ -> return ouid
      _ -> return ouid
      where
        ouid = idFromUnique $ edh'obj'ident o

    idOfProcDefi :: ProcDefi -> EdhValue
    idOfProcDefi !def = idFromUnique $ edh'procedure'ident def

    idOfProc :: EdhProcDefi -> EdhValue
    idOfProc (EdhIntrOp _ _ !def) =
      idFromUnique $ intrinsic'op'uniq def
    idOfProc (EdhOprtor _ _ _ !def) = idOfProcDefi def
    idOfProc (EdhMethod !def) = idOfProcDefi def
    idOfProc (EdhGnrtor !def) = idOfProcDefi def
    idOfProc (EdhIntrpr !def) = idOfProcDefi def
    idOfProc (EdhPrducr !def) = idOfProcDefi def
    idOfProc (EdhDescriptor !getter !maybeSetter) = case maybeSetter of
      Nothing -> idOfProcDefi getter
      Just !setter -> EdhPair (idOfProcDefi getter) (idOfProcDefi setter)

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
attrKeyStr (AttrByName !nm) = nm
attrKeyStr (AttrBySym (Symbol _ !symRepr)) = symRepr

attrKeyValue :: AttrKey -> EdhValue
attrKeyValue (AttrByName !nm) = EdhString nm
attrKeyValue (AttrBySym !sym) = EdhSymbol sym

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
  Nothing -> desc
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
mkDefault = mkDefault' $ ArgsPack [] odEmpty

mkDefault' :: ArgsPack -> Expr -> STM EdhValue
mkDefault' = mkDefault'' Nothing

mkDefault'' :: Maybe EdhThreadState -> ArgsPack -> Expr -> STM EdhValue
mkDefault'' !etsMaybe !apk !x = do
  !u <- unsafeIOToSTM newUnique
  return $ EdhDefault u apk x etsMaybe

-- | A list in Edh is a multable, singly-linked, prepend list.
data List = List !Unique !(TVar [EdhValue])

instance Eq List where
  List x'u _ == List y'u _ = x'u == y'u

instance Ord List where
  compare (List x'u _) (List y'u _) = compare x'u y'u

instance Hashable List where
  hashWithSalt s (List u _) = hashWithSalt s u

instance Show List where
  show (List _ !l) =
    if null ll
      then "[]"
      else "[ " ++ concat [show i ++ ", " | i <- ll] ++ "]"
    where
      ll = unsafePerformIO $ readTVarIO l

-- | The execution context of an Edh thread
data Context = Context
  { -- | the top frame of the calling context
    edh'ctx'tip :: !EdhCallFrame,
    -- | the underneath call frames
    edh'ctx'stack :: ![EdhCallFrame],
    -- | the direct generator caller
    edh'ctx'genr'caller :: !(Maybe EdhGenrCaller),
    -- | the match target value in context, normally be `true`, or the
    -- value from `x` in a `case x of` block
    edh'ctx'match :: EdhValue,
    -- | whether it's discouraged for procedure definitions or similar
    -- expressions from installing their results as attributes into the
    -- context scope
    edh'ctx'pure :: !Bool,
    -- | whether running within an exporting stmt
    edh'ctx'exp'target :: !(Maybe EntityStore),
    -- | whether running within an effect stmt
    edh'ctx'eff'target :: !(Maybe EntityStore)
  }

contextScope :: Context -> Scope
contextScope = edh'frame'scope . edh'ctx'tip

contextSrcLoc :: Context -> SrcLoc
contextSrcLoc = edh'exe'src'loc . edh'ctx'tip

callingScope :: Context -> Scope
callingScope = edh'frame'scope . callingFrame

callingSrcLoc :: Context -> SrcLoc
callingSrcLoc = edh'exe'src'loc . callingFrame

callingFrame :: Context -> EdhCallFrame
callingFrame (Context !tip _stack _ _ _ _ _) = tip

-- the yield receiver, a.k.a. the caller's continuation
type EdhGenrCaller =
  -- | one value yielded from the generator
  EdhValue ->
  -- | continuation of the genrator
  -- - Left (etsThrower, exv)
  --    exception thrown in processing that `yield`ed value
  -- - Right yieldResult
  --    result given back as the yielded value is processed,
  --    suitable to be the eval result of that `yield` action
  (Either (EdhThreadState, EdhValue) EdhValue -> STM ()) ->
  EdhTx

data EdhCallFrame = EdhCallFrame
  { -- | the scope of this call frame
    edh'frame'scope :: !Scope,
    -- | the source location currently under execution
    edh'exe'src'loc :: !SrcLoc,
    -- | cache of fallback effects to accelerate repeated resolution
    edh'effs'fb'cache ::
      !(TVar (Map.HashMap AttrKey (EdhValue, [EdhCallFrame]))),
    -- | the exception handler, `catch`/`finally` should capture the
    -- outer scope, and run its *tried* block with a new stack whose
    -- top frame is a scope all same but the `edh'exc'handler` field,
    -- which executes its handling logics appropriately.
    edh'exc'handler :: !EdhExcptHndlr
  }

newCallFrame :: Scope -> SrcLoc -> STM EdhCallFrame
newCallFrame !scope !src'loc = newCallFrame' scope src'loc defaultEdhExcptHndlr

newCallFrame' :: Scope -> SrcLoc -> EdhExcptHndlr -> STM EdhCallFrame
newCallFrame' !scope !src'loc !exh = do
  fbCache <- newTVar Map.empty
  return $ EdhCallFrame scope src'loc fbCache exh

frameMovePC :: EdhCallFrame -> SrcRange -> EdhCallFrame
frameMovePC !frame !src'span =
  frame
    { edh'exe'src'loc = loc {src'range = src'span}
    }
  where
    !loc = edh'exe'src'loc frame

etsMovePC :: EdhThreadState -> SrcRange -> EdhThreadState
etsMovePC !ets !src'span =
  ets
    { edh'context = ctx {edh'ctx'tip = frameMovePC tip src'span}
    }
  where
    !ctx = edh'context ets
    !tip = edh'ctx'tip ctx

type EdhExcptHndlr =
  -- | thread state of the thrower
  EdhThreadState ->
  -- | the error value to handle
  EdhValue ->
  -- | action to re-throw if not recovered
  (EdhValue -> STM ()) ->
  STM ()

defaultEdhExcptHndlr :: EdhExcptHndlr
defaultEdhExcptHndlr _etsThrower !exv !rethrow = rethrow exv

-- | A lexical scope
data Scope = Scope
  { -- | the backing storage of this scope
    edh'scope'entity :: !EntityStore,
    -- | `this` object in this scope
    edh'scope'this :: !Object,
    -- | `that` object in this scope
    edh'scope'that :: !Object,
    -- | the Edh procedure, as to run which, this scope is created
    -- note this is left lazy so the root scope can be created without infinite
    -- loop
    edh'scope'proc :: ProcDefi,
    -- | when this scope is of an effectful procedure as called, this is the
    -- outer call stack from which (but not including the) scope the effectful
    -- procedure is addressed of
    edh'effects'stack :: [EdhCallFrame]
  }

instance Show Scope where
  show !scope =
    T.unpack $
      "#scope: 📜 " <> procedureName sp
        <> " 🔎 "
        <> prettySrcLoc (edh'procedure'loc pd)
    where
      !sp = edh'scope'proc scope
      !pd = edh'procedure'decl sp

outerScopeOf :: Scope -> Maybe Scope
outerScopeOf !scope =
  if edh'scope'proc outerScope == edh'scope'proc scope
    then Nothing -- already at a root scope
    else Just outerScope
  where
    !outerScope = edh'procedure'lexi $ edh'scope'proc scope

rootScopeOf :: Scope -> Scope
rootScopeOf !scope =
  if edh'scope'proc outerScope == edh'scope'proc scope
    then scope -- found a root scope
    else rootScopeOf outerScope
  where
    !outerScope = edh'procedure'lexi $ edh'scope'proc scope

edhScopeSrcLoc :: Scope -> SrcLoc
edhScopeSrcLoc !scope = case edh'procedure'decl $ edh'scope'proc scope of
  HostDecl {} -> SrcLoc (SrcDoc "<host-world>") noSrcRange
  ProcDecl _ _ _ (StmtSrc _ !body'span) !loc -> loc {src'range = body'span}

-- | A class is wrapped as an object per se, the object's storage structure is
-- here:
-- - the procedure created the class, from which the class name, the lexical
--   scope and other information can be obtained
-- - a hash storage of (so called static) attributes shared by all object
--   instances of the class
-- - the storage allocator for new objects of the class to be created
data Class = Class
  { edh'class'proc :: !ProcDefi,
    edh'class'store :: !EntityStore,
    edh'class'allocator :: !(ArgsPack -> EdhObjectAllocator),
    -- | the C3 linearized method resolution order, with self omitted
    edh'class'mro :: !(TVar [Object])
  }

instance Show Class where
  show cls = ("class:" <>) $ T.unpack $ procedureName $ edh'class'proc cls

instance Eq Class where
  Class x'p _ _ _ == Class y'p _ _ _ = x'p == y'p

instance Hashable Class where
  hashWithSalt s (Class p _ _ _) = hashWithSalt s p

type EdhObjectAllocator = EdhAllocExit -> EdhTx

type EdhAllocExit = Maybe Unique -> ObjectStore -> STM ()

objClass :: Object -> Class
objClass !obj = case edh'obj'store $ edh'obj'class obj of
  ClassStore !cls -> cls
  _ -> error "bug: class of an object not bearing ClassStore"

edhClassName :: Object -> Text
edhClassName !clsObj = case edh'obj'store clsObj of
  ClassStore !cls -> procedureName $ edh'class'proc cls
  _ -> "<bogus-class>"

objClassName :: Object -> Text
objClassName = edhClassName . edh'obj'class

objClassProc :: Object -> ProcDefi
objClassProc = edhClassProc . edh'obj'class
  where
    edhClassProc :: Object -> ProcDefi
    edhClassProc !clsObj = case edh'obj'store clsObj of
      ClassStore !cls -> edh'class'proc cls
      _ -> error "bug: not a class"

-- | An object views an entity, with inheritance relationship
-- to any number of super objects.
data Object = Object
  { -- | unique identifier of an Edh object
    edh'obj'ident :: !Unique,
    -- | the storage for entity attributes of the object
    edh'obj'store :: !ObjectStore,
    -- | the class object must have a 'ClassStore' storage
    -- note this field can not be strict, or it's infinite loop creating the
    -- meta class object (whose class is itself)
    edh'obj'class :: Object,
    -- | up-links for object inheritance hierarchy
    edh'obj'supers :: !(TVar [Object])
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

data ObjectStore
  = HashStore !EntityStore
  | ClassStore !Class -- in case this is a class object
  | HostStore !Dynamic

instance Show ObjectStore where
  show HashStore {} = "<<HashStore>>"
  show (ClassStore cls) = "<<ClassStore:" <> show cls <> ">>"
  show (HostStore (Dynamic tr _)) = "<<HostStore:" <> show tr <> ">>"

-- | Try cast and unveil an Object's storage of a known type, while not
-- considering any super object eligible
castObjSelfStore :: forall a. (Typeable a) => Object -> STM (Maybe a)
castObjSelfStore !obj = case edh'obj'store obj of
  HostStore !hsd -> case fromDynamic hsd of
    Just (hsv :: a) -> return $ Just hsv
    Nothing -> return Nothing
  _ -> return Nothing

-- | Try cast and unveil a possible Object's storage of a known type, while not
-- considering any super object eligible
castObjSelfStore' :: forall a. (Typeable a) => EdhValue -> STM (Maybe a)
castObjSelfStore' !val = case edhUltimate val of
  EdhObject !obj -> castObjSelfStore obj
  _ -> return Nothing

-- | Try cast and unveil an Object's storage of a known type
castObjectStore :: forall a. (Typeable a) => Object -> STM (Maybe (Object, a))
castObjectStore !obj = readTVar (edh'obj'supers obj) >>= goSearch . (obj :)
  where
    goSearch [] = return Nothing
    goSearch (o : rest) =
      castObjSelfStore o >>= \case
        Just !d -> return $ Just (o, d)
        Nothing -> goSearch rest

-- | Try cast and unveil a possible Object's storage of a known type
castObjectStore' ::
  forall a. (Typeable a) => EdhValue -> STM (Maybe (Object, a))
castObjectStore' !val = case edhUltimate val of
  EdhObject !obj -> castObjectStore obj
  _ -> return Nothing

-- | A world for Edh programs to change
data EdhWorld = EdhWorld
  { -- | root scope of this world
    edh'world'root :: !Scope,
    -- | sandbox scope of this world
    edh'world'sandbox :: !Scope,
    -- | all operators declared in this world
    edh'world'operators :: !(TVar GlobalOpDict),
    -- | all modules loaded, being loaded, or failed loading into this world
    edh'world'modules :: !(TMVar (Map.HashMap ModuleId (TVar ModuSlot))),
    -- | all fragments cached (after successfully parsed) in this world
    edh'world'fragments :: !(TVar (Map.HashMap ModuleFile CachedFrag)),
    -- | for console logging, input and output
    edh'world'console :: !EdhConsole,
    -- | wrapping any host value as object
    edh'value'wrapper :: !(Maybe Text -> Dynamic -> STM Object),
    -- wrapping a scope as object for reflective purpose
    edh'scope'wrapper :: !(Scope -> STM Object),
    -- | world root effects
    edh'root'effects ::
      !(TVar (Map.HashMap AttrKey (EdhValue, [EdhCallFrame]))),
    -- wrapping a host exceptin as an Edh object
    edh'exception'wrapper ::
      !(Maybe EdhThreadState -> SomeException -> STM Object),
    -- the class of module objects
    edh'module'class :: !Object,
    -- the number of times a metric trap is requested
    --
    -- an Edh thread should maintain the last request number it has responded
    -- to, and do respond (e.g. print out the backtrace & time cost of previous
    -- and/or next STM transaction) to each new request it sees
    edh'trap'request :: !(IORef Int)
  }

instance Eq EdhWorld where
  x == y =
    edh'scope'this (edh'world'root x) == edh'scope'this (edh'world'root y)

data ModuleId = HostModule !ModuleName | EdhModule !ModuleFile
  deriving (Eq)

instance Hashable ModuleId where
  hashWithSalt s (HostModule name) =
    s `hashWithSalt` (1 :: Int) `hashWithSalt` name
  hashWithSalt s (EdhModule file) =
    s `hashWithSalt` (2 :: Int) `hashWithSalt` file

data ModuSlot
  = ModuLoaded !Object
  | ModuLoading !Scope !(TVar [Either EdhValue Object -> STM ()])
  | ModuFailed !EdhValue

data CachedFrag = CachedFrag !EpochTime !Text ![StmtSrc]

createEdhModule :: EdhWorld -> Text -> String -> IO Object
createEdhModule !world !moduName !srcName = do
  !idModu <- newUnique
  !hs <-
    atomically $
      iopdFromList
        [ (AttrByName "__name__", EdhString moduName),
          (AttrByName "__file__", EdhString $ T.pack srcName)
        ]
  !ss <- newTVarIO []
  return
    Object
      { edh'obj'ident = idModu,
        edh'obj'store = HashStore hs,
        edh'obj'class = edh'module'class world,
        edh'obj'supers = ss
      }

worldContext :: EdhWorld -> Context
worldContext !world =
  Context
    { edh'ctx'tip =
        EdhCallFrame
          (edh'world'root world)
          (SrcLoc (SrcDoc "<world>") noSrcRange)
          (edh'root'effects world)
          defaultEdhExcptHndlr,
      edh'ctx'stack = [],
      edh'ctx'genr'caller = Nothing,
      edh'ctx'match = true,
      edh'ctx'pure = False,
      edh'ctx'exp'target = Nothing,
      edh'ctx'eff'target = Nothing
    }
{-# INLINE worldContext #-}

-- | Checkout 'defaultEdhConsole' and 'defaultEdhIOLoop' from the
-- default batteries for implementation details, or just use that.
data EdhConsole = EdhConsole
  { consoleIO :: !(EdhConsoleIO -> IO ()),
    consoleIOLoop :: IO (),
    consoleLogLevel :: !LogLevel,
    consoleLogger :: !EdhLogger,
    consoleFlush :: IO ()
  }

data EdhConsoleIO
  = ConsoleShutdown
  | -- | output a line
    ConsoleOut !Text
  | -- | read input into the var, with ps1 ps2
    --   ps1 is single line prompt, ps2 for multil-line
    ConsoleIn !(TMVar EdhInput) !Text !Text
  deriving (Eq)

data EdhInput = EdhInput
  { edh'input'src'name :: !Text,
    edh'input'1st'line :: !Int,
    edh'input'src'lines :: ![Text]
  }
  deriving (Eq, Show)

type EdhLogger = LogLevel -> Maybe Text -> Text -> STM ()

type LogLevel = Int

-- | The state of an Edh program
data EdhProgState = EdhProgState
  { edh'prog'world :: !EdhWorld,
    edh'prog'main :: !ThreadId,
    edh'prog'result :: !(TMVar (Either SomeException EdhValue)),
    edh'fork'queue :: !(TBQueue (EdhThreadState, EdhThreadState -> STM ()))
  }

-- | The state of an Edh thread belonging to an Edh program
data EdhThreadState = EdhThreadState
  { edh'thread'prog :: !EdhProgState,
    edh'in'tx :: !Bool,
    edh'task'queue :: !(TBQueue EdhTask),
    edh'perceivers :: !(TVar [PerceiveRecord]),
    edh'defers :: !(TVar [DeferRecord]),
    edh'context :: !Context
  }

-- | The task to be queued for execution of an Edh thread.
--
-- the thread state provides the context, into which an exception should be
-- thrown, if one ever occurs during the action.
--
-- an action should return True to signal intended termination of the thread,
-- or False to continue normally.
data EdhTask
  = EdhDoIO !EdhThreadState !(IO Bool)
  | EdhDoSTM !EdhThreadState !(STM Bool)

data PerceiveRecord = PerceiveRecord
  { -- | chan subscribed to source event sink
    edh'perceive'chan :: !(TChan EdhValue),
    -- | origin ets upon the perceiver is armed
    edh'perceive'ets :: !EdhThreadState,
    -- | reacting action per event received, event value is context match
    edh'perceive'act :: !(TVar Bool -> EdhTx)
  }

data DeferRecord = DeferRecord
  { -- | origin ets upon the deferred action is scheduled
    edh'defer'ets :: !EdhThreadState,
    -- | deferred action to be performed upon termination of the target Edh
    -- thread
    edh'defer'act :: !(EdhThreadState -> STM ())
  }

-- | Perform a subsquent STM action within an Edh thread, honoring
-- @edh'in'tx ets@ in deciding whether to do it in current STM transaction, or
-- to do it in a separate, later STM transaction, which is scheduled by putting
-- the action into the Edh thread's task queue.
--
-- @edh'in'tx ets@ is normally controlled by the `ai` keyword at scripting
-- level, this implements the semantics of it
edhDoSTM :: EdhThreadState -> STM () -> STM ()
edhDoSTM !ets !act =
  if edh'in'tx ets
    then act
    else writeTBQueue (edh'task'queue ets) $ EdhDoSTM ets $ False <$ act
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
type EdhTxExit a = a -> EdhTx

endOfEdh :: EdhTxExit a
endOfEdh _ _ = return ()
{-# INLINE endOfEdh #-}

seqEdhTx :: forall a. [EdhTxExit a -> EdhTx] -> EdhTxExit [a] -> EdhTx
seqEdhTx !xs !exit = go xs []
  where
    go :: [EdhTxExit a -> EdhTx] -> [a] -> EdhTx
    go [] ys = exit $! reverse ys
    go (x : rest) ys = x $ \y -> go rest (y : ys)
{-# INLINE seqEdhTx #-}

-- | Schedule forking of a GHC thread to bootstrap an Edh thread to run the
-- specified Edh computation, with the specified thread state modifer applied
-- before the computation is stated in the descendant thread.
--
-- NOTE this happens as part of current STM tx, the actual fork won't happen if
--      any subsequent Edh code within the tx throws without recovered
forkEdh :: (EdhThreadState -> EdhThreadState) -> EdhTx -> EdhTxExit () -> EdhTx
forkEdh !bootMod !p !exit !etsForker = do
  writeTBQueue
    (edh'fork'queue $ edh'thread'prog etsForker)
    (etsForker, p . bootMod)
  exitEdh etsForker exit ()
{-# INLINE forkEdh #-}

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
exitEdhTx :: EdhTxExit a -> a -> EdhTx
exitEdhTx !exit !val !ets = edhDoSTM ets $ exit val ets
{-# INLINE exitEdhTx #-}

-- | Exit an Edh computation from STM monad in CPS.
--
-- @edh'in'tx ets@ is normally controlled by the `ai` keyword at scripting
-- level, this implements the semantics of it
exitEdh :: EdhThreadState -> EdhTxExit a -> a -> STM ()
exitEdh !ets !exit !val = edhDoSTM ets $ exit val ets
{-# INLINE exitEdh #-}

-- | Type of an intrinsic infix operator in the host language (Haskell).
--
-- Note no stack frame is created/pushed when an intrinsic operator is called.
type EdhIntrinsicOp = ExprSrc -> ExprSrc -> EdhTxExit EdhValue -> EdhTx

edhFlipOp :: EdhIntrinsicOp -> EdhIntrinsicOp
edhFlipOp !op = flipped
  where
    flipped :: EdhIntrinsicOp
    flipped !lhExpr !rhExpr !exit = op rhExpr lhExpr exit

data IntrinOpDefi = IntrinOpDefi
  { intrinsic'op'uniq :: !Unique,
    intrinsic'op'symbol :: !AttrName,
    intrinsic'op :: EdhIntrinsicOp
  }

-- | Polytype to denote Haskell procedures runnable by an Edh language runtime
type EdhProc a = EdhTxExit a -> EdhTx

-- | Monotype for the last part of an 'EdhCallable' procedure
-- such a procedure servs as the callee, it is in CPS, i.e. taking an exit to
-- return a value from this procedure
type EdhHostProc = EdhTxExit EdhValue -> EdhTx

-- | An event sink is similar to a Go channel, but is broadcast
-- in nature, in contrast to the unicast nature of channels in Go.
data Sink = Sink
  { sink'uniq :: !Unique,
    -- | most recent value for the lingering copy of an event sink
    --
    -- an event sink always starts out being the original lingering copy,
    -- then one or more non-lingering, shadow copies of the original copy can
    -- be obtained by `s.subseq` where `s` is either a lingering copy or
    -- non-lingering copy
    --
    -- a non-lingering copy has this field being Nothing
    sink'mrv :: !(Maybe (TVar EdhValue)),
    -- | the broadcast channel
    sink'chan :: !(TChan EdhValue),
    -- | a chain of atomic actions to be injected into the publishing
    -- transaction for an event
    sink'atoms :: TVar (EdhValue -> STM ()),
    -- | subscriber counter, will remain negative once the sink is marked eos
    -- (by publishing a `nil` value into it), or increase every time the sink
    -- is subscribed (a subscriber's channel dup'ped from `sink'chan`)
    sink'subc :: !(TVar Int)
  }

instance Eq Sink where
  Sink x'u _ _ _ _ == Sink y'u _ _ _ _ = x'u == y'u

instance Ord Sink where
  compare (Sink x'u _ _ _ _) (Sink y'u _ _ _ _) = compare x'u y'u

instance Hashable Sink where
  hashWithSalt s (Sink s'u _ _ _ _) = hashWithSalt s s'u

instance Show Sink where
  show Sink {} = "<sink>"

-- | executable precedures
data EdhProcDefi
  = EdhIntrOp !OpFixity !Precedence !IntrinOpDefi
  | EdhOprtor !OpFixity !Precedence !(Maybe EdhValue) !ProcDefi
  | EdhMethod !ProcDefi
  | EdhGnrtor !ProcDefi
  | EdhIntrpr !ProcDefi
  | EdhPrducr !ProcDefi
  | -- similar to Python Descriptor
    -- with a getter method and optionally a settor method, for properties
    -- (programmatically managed attributes) to be defined on objects
    -- deleter semantic is expressed as calling setter without arg
    EdhDescriptor !ProcDefi !(Maybe ProcDefi)

instance Show EdhProcDefi where
  show (EdhIntrOp !fixity !prec (IntrinOpDefi _ !opSym _)) =
    "intrinsic: "
      ++ show fixity
      ++ " "
      ++ show prec
      ++ " ("
      ++ T.unpack opSym
      ++ ")"
  show (EdhOprtor !fixity !prec _pred !pd) =
    "operator: "
      ++ show fixity
      ++ " "
      ++ show prec
      ++ " ("
      ++ T.unpack (procedureName pd)
      ++ ")"
  show (EdhMethod !pd) = T.unpack ("method: " <> procedureName pd)
  show (EdhGnrtor !pd) = T.unpack ("generator: " <> procedureName pd)
  show (EdhIntrpr !pd) = T.unpack ("interpreter: " <> procedureName pd)
  show (EdhPrducr !pd) = T.unpack ("producer: " <> procedureName pd)
  show (EdhDescriptor !getter !setter) =
    (<> T.unpack (procedureName getter) <> ">") $ case setter of
      Nothing -> "readonly property "
      Just _ -> "property "

instance Eq EdhProcDefi where
  EdhIntrOp _ _ (IntrinOpDefi x'u _ _) == EdhIntrOp _ _ (IntrinOpDefi y'u _ _) =
    x'u == y'u
  EdhOprtor _ _ _ x == EdhOprtor _ _ _ y = x == y
  EdhMethod x == EdhMethod y = x == y
  EdhGnrtor x == EdhGnrtor y = x == y
  EdhIntrpr x == EdhIntrpr y = x == y
  EdhPrducr x == EdhPrducr y = x == y
  EdhDescriptor x'getter x'setter == EdhDescriptor y'getter y'setter =
    x'getter == y'getter && x'setter == y'setter
  _ == _ = False

instance Hashable EdhProcDefi where
  hashWithSalt s (EdhIntrOp _ _ (IntrinOpDefi x'u _ _)) = hashWithSalt s x'u
  hashWithSalt s (EdhMethod x) = hashWithSalt s x
  hashWithSalt s (EdhOprtor _ _ _ x) = hashWithSalt s x
  hashWithSalt s (EdhGnrtor x) = hashWithSalt s x
  hashWithSalt s (EdhIntrpr x) = hashWithSalt s x
  hashWithSalt s (EdhPrducr x) = hashWithSalt s x
  hashWithSalt s (EdhDescriptor getter setter) =
    s `hashWithSalt` getter `hashWithSalt` setter

callableName :: EdhProcDefi -> Text
callableName = \case
  EdhIntrOp _fixity _preced (IntrinOpDefi _ !opSym _) -> "(" <> opSym <> ")"
  EdhOprtor _fixity _preced _ !pd -> "(" <> procedureName pd <> ")"
  EdhMethod !pd -> procedureName pd
  EdhGnrtor !pd -> procedureName pd
  EdhIntrpr !pd -> procedureName pd
  EdhPrducr !pd -> procedureName pd
  EdhDescriptor !getter !setter ->
    (<> procedureName getter <> ">") $ case setter of
      Nothing -> "<readonly property "
      Just _ -> "<property "

callableDoc :: EdhProcDefi -> OptDocCmt
callableDoc = \case
  EdhIntrOp _fixity _preced _ -> NoDocCmt
  EdhOprtor _fixity _preced _ !pd -> edh'procedure'doc pd
  EdhMethod !pd -> edh'procedure'doc pd
  EdhGnrtor !pd -> edh'procedure'doc pd
  EdhIntrpr !pd -> edh'procedure'doc pd
  EdhPrducr !pd -> edh'procedure'doc pd
  EdhDescriptor !getter !maybeSetter -> case maybeSetter of
    Nothing -> edh'procedure'doc getter
    Just setter -> edh'procedure'doc setter

callableLoc :: EdhProcDefi -> SrcLoc
callableLoc = \case
  EdhIntrOp _fixity _preced _ -> SrcLoc (SrcDoc "<host-world>") noSrcRange
  EdhOprtor _fixity _preced _ !pd -> procedureLoc' pd
  EdhMethod !pd -> procedureLoc' pd
  EdhGnrtor !pd -> procedureLoc' pd
  EdhIntrpr !pd -> procedureLoc' pd
  EdhPrducr !pd -> procedureLoc' pd
  EdhDescriptor !getter !maybeSetter -> case maybeSetter of
    Nothing -> procedureLoc' getter
    Just setter -> procedureLoc' setter

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

data EdhBound = OpenBound EdhValue | ClosedBound EdhValue
  deriving (Eq)

edhBoundValue :: EdhBound -> EdhValue
edhBoundValue (OpenBound v) = v
edhBoundValue (ClosedBound v) = v

edhBoundMarkChar :: EdhBound -> Text
edhBoundMarkChar OpenBound {} = "^"
edhBoundMarkChar ClosedBound {} = ""

instance Hashable EdhBound where
  hashWithSalt s (OpenBound b) = s `hashWithSalt` (1 :: Int) `hashWithSalt` b
  hashWithSalt s (ClosedBound b) = s `hashWithSalt` (2 :: Int) `hashWithSalt` b

-- | everything is a value in Edh
data EdhValue
  = -- term values (immutable)
    EdhNil
  | EdhDecimal !Decimal
  | EdhBool !Bool
  | EdhBlob !ByteString
  | EdhString !Text
  | EdhSymbol !Symbol
  | EdhUUID !UUID.UUID
  | -- range with lower & upper bounds
    EdhRange !EdhBound !EdhBound
  | -- immutable containers
    --   the elements may still pointer to mutable data
    EdhPair !EdhValue !EdhValue
  | EdhArgsPack ArgsPack
  | -- | mutable containers
    EdhDict !Dict
  | EdhList !List
  | -- | an Edh object can either be an entity backed by a hash store, or
    -- wraps some host data dynamically mutable, while a class object as a
    -- special case, can construct other objects being its instances, and
    -- the class object's entity attributes are shared by those instances as
    -- static attributes
    EdhObject !Object
  | -- | a callable procedure
    -- with the effect outer stack if resolved as an effectful artifact
    EdhProcedure !EdhProcDefi !(Maybe [EdhCallFrame])
  | -- | a callable procedure bound to a specific this object and that object
    -- with the effect outer stack if resolved as an effectful artifact
    EdhBoundProc !EdhProcDefi !Object !Object !(Maybe [EdhCallFrame])
  | -- flow control
    EdhBreak
  | EdhContinue
  | EdhCaseClose !EdhValue
  | EdhCaseOther
  | EdhFallthrough
  | EdhRethrow
  | EdhYield !EdhValue
  | EdhReturn !EdhValue
  | EdhOrd !Ordering
  | -- | prefer better efforted result, but can default to the specified expr
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
    --   a conclusion of not/applicable at all
    --
    -- the apk can be used to pass back intermediate result values evaluated
    -- from expressions, e.g lhs and rhs of an infix operator, to avoid
    -- duplicate evaluation of expressions involved
    EdhDefault !Unique !ArgsPack !Expr !(Maybe EdhThreadState)
  | -- | event sink
    EdhSink !Sink
  | -- | named value, a.k.a. term definition
    EdhNamedValue !AttrName !EdhValue
  | -- | unit of measure definition
    EdhUoM !UnitDefi
  | -- | quantity with associated unit of measure
    EdhQty !Quantity
  | -- | 1st class expression value, with source (or not, if empty)
    EdhExpr !ExprDefi !Text

instance Deletable EdhValue where
  -- `nil` carries deletion semantics
  impliesDeletionAtRHS EdhNil = True
  impliesDeletionAtRHS _ = False

instance Show EdhValue where
  show EdhNil = "nil"
  show (EdhDecimal v) = showDecimal v
  show (EdhBool v) = if v then "true" else "false"
  show (EdhBlob b) = "<blob#" <> show (B.length b) <> ">"
  show (EdhString v) = show v
  show (EdhSymbol v) = show v
  show (EdhUUID v) = "UUID('" <> UUID.toString v <> "')"
  show (EdhRange (ClosedBound lower) (ClosedBound upper)) =
    show lower <> " .. " <> show upper
  show (EdhRange (OpenBound lower) (ClosedBound upper)) =
    show lower <> " ^.. " <> show upper
  show (EdhRange (ClosedBound lower) (OpenBound upper)) =
    show lower <> " ..^ " <> show upper
  show (EdhRange (OpenBound lower) (OpenBound upper)) =
    show lower <> " ^..^ " <> show upper
  show (EdhPair k v) = show k <> ":" <> show v
  show (EdhArgsPack v) = show v
  show (EdhDict v) = show v
  show (EdhList v) = show v
  show (EdhObject v) = show v
  show (EdhProcedure !pc _) = "<callable:" ++ show pc ++ ">"
  show (EdhBoundProc !pc _ _ _) = "<bound:" ++ show pc ++ ">"
  show EdhBreak = "<break>"
  show EdhContinue = "<continue>"
  show (EdhCaseClose v) = "<caseclose: " ++ show v ++ ">"
  show EdhCaseOther = "<caseother>"
  show EdhFallthrough = "<fallthrough>"
  show EdhRethrow = "<rethrow>"
  show (EdhYield v) = "<yield: " ++ show v ++ ">"
  show (EdhReturn v) = "<return: " ++ show v ++ ">"
  show (EdhOrd ord) = show ord
  show (EdhDefault _ apk x _) = case x of
    ExprWithSrc _ [SrcSeg src] ->
      "default " <> show apk <> " " <> T.unpack src
    _ -> "<default: " ++ show apk ++ " " ++ show x ++ ">"
  show (EdhSink v) = show v
  show (EdhNamedValue n v@EdhNamedValue {}) =
    -- Edh operators are all left-associative, parenthesis needed
    T.unpack n <> " := (" <> show v <> ")"
  show (EdhNamedValue n v) = T.unpack n <> " := " <> show v
  show (EdhUoM defi) = show defi
  show (EdhQty q) = show q
  show (EdhExpr (ExprDefi _ x _) s) =
    if T.null s
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
  EdhNil == EdhNil = True
  EdhDecimal x == EdhDecimal y = x == y
  EdhBool x == EdhBool y = x == y
  EdhBlob x == EdhBlob y = x == y
  EdhString x == EdhString y = x == y
  EdhSymbol x == EdhSymbol y = x == y
  EdhUUID x == EdhUUID y = x == y
  EdhRange x'l x'u == EdhRange y'l y'u = x'l == y'l && x'u == y'u
  EdhPair x'k x'v == EdhPair y'k y'v = x'k == y'k && x'v == y'v
  EdhArgsPack x == EdhArgsPack y = x == y
  EdhDict x == EdhDict y = x == y
  EdhList x == EdhList y = x == y
  EdhObject x == EdhObject y = x == y
  EdhProcedure x _ == EdhProcedure y _ = x == y
  EdhBoundProc x x'this x'that _ == EdhBoundProc y y'this y'that _ =
    x == y && x'this == y'this && x'that == y'that
  EdhBreak == EdhBreak = True
  EdhContinue == EdhContinue = True
  EdhCaseClose x == EdhCaseClose y = x == y
  EdhCaseOther == EdhCaseOther = True
  EdhFallthrough == EdhFallthrough = True
  EdhRethrow == EdhRethrow = True
  -- todo: regard a yielded/returned value equal to the value itself ?
  EdhYield x'v == EdhYield y'v = x'v == y'v
  EdhReturn x'v == EdhReturn y'v = x'v == y'v
  EdhOrd x == EdhOrd y = x == y
  EdhDefault x'u _ _ _ == EdhDefault y'u _ _ _ = x'u == y'u
  EdhSink x == EdhSink y = x == y
  EdhNamedValue x'n x'v == EdhNamedValue y'n y'v = x'n == y'n && x'v == y'v
  EdhNamedValue _ x'v == y = x'v == y
  x == EdhNamedValue _ y'v = x == y'v
  EdhExpr (ExprDefi _ (LitExpr x'l) _) _
    == EdhExpr (ExprDefi _ (LitExpr y'l) _) _ =
      x'l == y'l
  EdhExpr (ExprDefi x'u _ _) _ == EdhExpr (ExprDefi y'u _ _) _ = x'u == y'u
  (EdhUoM x) == (EdhUoM y) = x == y
  (EdhQty x) == (EdhQty y) = x == y
  -- todo: support coercing equality ?
  --       * without this, we are a strongly typed dynamic language
  --       * with this, we'll be a weakly typed dynamic language
  _ == _ = False

instance Hashable EdhValue where
  hashWithSalt s EdhNil = hashWithSalt s (0 :: Int)
  hashWithSalt s (EdhDecimal x) = hashWithSalt s x
  hashWithSalt s (EdhBool x) = hashWithSalt s x
  hashWithSalt s (EdhBlob x) = hashWithSalt s x
  hashWithSalt s (EdhString x) = hashWithSalt s x
  hashWithSalt s (EdhSymbol x) = hashWithSalt s x
  hashWithSalt s (EdhUUID x) = hashWithSalt s x
  hashWithSalt s (EdhRange l u) = s `hashWithSalt` l `hashWithSalt` u
  hashWithSalt s (EdhPair k v) = s `hashWithSalt` k `hashWithSalt` v
  hashWithSalt s (EdhArgsPack x) = hashWithSalt s x
  hashWithSalt s (EdhDict x) = hashWithSalt s x
  hashWithSalt s (EdhList x) = hashWithSalt s x
  hashWithSalt s (EdhObject x) = hashWithSalt s x
  hashWithSalt s (EdhProcedure x _) = hashWithSalt s x
  hashWithSalt s (EdhBoundProc x this that _) =
    s `hashWithSalt` x `hashWithSalt` this `hashWithSalt` that
  hashWithSalt s EdhBreak = hashWithSalt s (-1 :: Int)
  hashWithSalt s EdhContinue = hashWithSalt s (-2 :: Int)
  hashWithSalt s (EdhCaseClose v) =
    s `hashWithSalt` (-3 :: Int) `hashWithSalt` v
  hashWithSalt s EdhCaseOther = hashWithSalt s (-4 :: Int)
  hashWithSalt s EdhFallthrough = hashWithSalt s (-5 :: Int)
  hashWithSalt s EdhRethrow = hashWithSalt s (-6 :: Int)
  hashWithSalt s (EdhYield v) = s `hashWithSalt` (-7 :: Int) `hashWithSalt` v
  hashWithSalt s (EdhReturn v) = s `hashWithSalt` (-8 :: Int) `hashWithSalt` v
  hashWithSalt s (EdhOrd o) = s `hashWithSalt` (-10 :: Int) `hashWithSalt` o
  hashWithSalt s (EdhDefault u _ _ _) =
    s `hashWithSalt` (-9 :: Int) `hashWithSalt` u
  hashWithSalt s (EdhSink x) = hashWithSalt s x
  hashWithSalt s (EdhNamedValue _ v) = hashWithSalt s v
  hashWithSalt s (EdhUoM defi) =
    s `hashWithSalt` (-11 :: Int) `hashWithSalt` defi
  hashWithSalt s (EdhQty q) = s `hashWithSalt` (-12 :: Int) `hashWithSalt` q
  hashWithSalt s (EdhExpr (ExprDefi _ (LitExpr l) _) _) = hashWithSalt s l
  hashWithSalt s (EdhExpr (ExprDefi u _ _) _) = hashWithSalt s u

edhDeReturn :: EdhValue -> EdhValue
edhDeReturn (EdhReturn !val) = edhDeReturn val
edhDeReturn (EdhYield !val) = edhDeReturn val
edhDeReturn (EdhCaseClose !val) = edhDeReturn val
edhDeReturn EdhCaseOther = nil
edhDeReturn !val = val

edhDeCaseClose :: EdhValue -> EdhValue
edhDeCaseClose (EdhCaseClose !val) = edhDeCaseClose val
edhDeCaseClose !val = val

edhDeCaseWrap :: EdhValue -> EdhValue
edhDeCaseWrap (EdhCaseClose !val) = edhDeCaseWrap val
edhDeCaseWrap EdhCaseOther = nil
edhDeCaseWrap EdhFallthrough = nil
edhDeCaseWrap !val = val

edhDeFlowCtrl :: EdhValue -> EdhValue
edhDeFlowCtrl (EdhCaseClose !val) = edhDeFlowCtrl val
edhDeFlowCtrl EdhCaseOther = nil
edhDeFlowCtrl EdhFallthrough = nil
edhDeFlowCtrl EdhBreak = nil
edhDeFlowCtrl EdhContinue = nil
edhDeFlowCtrl !val = val

edhUltimate :: EdhValue -> EdhValue
edhUltimate (EdhNamedValue _ !v) = edhUltimate v
edhUltimate (EdhReturn !v) = edhUltimate v
edhUltimate (EdhYield !v) = edhUltimate v
edhUltimate !v = edhDeCaseWrap v

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

-- | Similar to `None`
--
-- though we don't have `Maybe` monad in Edh, having a `Nothing`
-- carrying null semantic may be useful in some cases.
edhNothing :: EdhValue
edhNothing = EdhNamedValue "Nothing" EdhNil

-- | NA for not-applicable, similar to @NotImplemented@ as in Python
edhNA :: EdhValue
edhNA =
  EdhNamedValue "NA" $
    EdhDefault
      (unsafePerformIO newUnique)
      (ArgsPack [] odEmpty)
      (ExprWithSrc (ExprSrc (LitExpr NilLiteral) noSrcRange) [SrcSeg "nil"])
      Nothing
{-# NOINLINE edhNA #-}

-- | With `nil` converted to `None` so the result will never be `nil`.
--
-- As `nil` carries *delete* semantic in assignment, in some cases it's better
-- avoided.
edhNonNil :: EdhValue -> EdhValue
edhNonNil EdhNil = edhNone
edhNonNil !v = v

nan :: EdhValue
nan = EdhDecimal D.nan

inf :: EdhValue
inf = EdhDecimal D.inf

true :: EdhValue
true = EdhBool True

false :: EdhValue
false = EdhBool False

data StmtSrc = StmtSrc !Stmt !SrcRange
  deriving (Eq)

instance Show StmtSrc where
  show (StmtSrc s _) = show s

stmtSrcSpan :: StmtSrc -> SrcRange
stmtSrcSpan (StmtSrc _ !s'span) = s'span

optDocCmt :: Maybe [Text] -> OptDocCmt
optDocCmt Nothing = NoDocCmt
optDocCmt (Just !lines_) = DocCmt lines_

data OptDocCmt = NoDocCmt | DocCmt [Text]
  deriving (Eq)

instance Show OptDocCmt where
  show NoDocCmt = "<no-doc>"
  show (DocCmt []) = "<empty-doc>"
  show (DocCmt lns) = "<" <> show (length lns) <> "-doc-lines>"

mergeDocCmts :: OptDocCmt -> OptDocCmt -> OptDocCmt
mergeDocCmts NoDocCmt cmt = cmt
mergeDocCmts cmt NoDocCmt = cmt
mergeDocCmts (DocCmt lns1) (DocCmt lns2) =
  DocCmt $ lns1 ++ ["---"] ++ lns2

data Stmt
  = -- | literal `pass` to fill a place where a statement needed,
    -- same as in Python
    VoidStmt
  | IllegalSegment !Text !SrcPos
  | -- | similar to `go` in Go, starts goroutine
    GoStmt !ExprSrc
  | -- | not similar to `defer` in Go (in Go `defer` snapshots arg values
    -- and schedules execution on func return), but in Edh `defer`
    -- schedules execution on thread termination
    DeferStmt !ExprSrc
  | -- | artifacts introduced within an `effect` statement will be put
    -- into effect namespace, which as currently implemented, a dict
    -- resides in current scope entity addressed by name `__exports__`
    EffectStmt !ExprSrc !OptDocCmt
  | -- | assignment with args (un/re)pack sending/receiving syntax
    LetStmt !ArgsReceiver !ArgsPacker
  | -- | unit of measure declaration
    UnitStmt ![UnitDecl] !OptDocCmt
  | -- | super object declaration for a descendant object
    ExtendsStmt !ExprSrc
  | -- | perceiption declaration, a perceiver is bound to an event `sink`
    -- with the calling thread as context, when an event fires from that
    -- event `sink`, the bound perceiver body will be executed from the
    -- thread where it's declared, after the currernt transaction on that
    -- thread finishes, a perceiver body can `break` to terminate that
    -- particular thread, or the thread will continue to process next
    -- perceiver, if no perceiver does `break`, next transactional task
    -- is carried on as normally.
    --
    -- the perceiver body uses a value/pattern matching branch, or a
    -- group of branches (in a block expr) to handle the happened event
    -- data, including `nil` as end-of-stream indicator.
    --
    -- the perceiption construct is somewhat similar to unix signal handling
    PerceiveStmt !ExprSrc !ExprSrc
  | -- | break from a while/for loop, or terminate the Edh thread if given
    -- from a perceiver
    BreakStmt
  | -- | continue a while/for loop
    ContinueStmt
  | -- | similar to fallthrough in Go
    FallthroughStmt
  | -- | rethrow current exception
    RethrowStmt
  | -- | any value can be thrown as exception, handling will rely on the
    --   ($=>) as `catch` and (@=>) as `finally` operators
    ThrowStmt !ExprSrc
  | -- | early stop from a procedure
    ReturnStmt !ExprSrc !OptDocCmt
  | -- | expression with precedence
    ExprStmt !Expr !OptDocCmt
  deriving (Eq, Show)

enExpr :: StmtSrc -> ExprSrc
enExpr (StmtSrc (ExprStmt x _) src'span) = ExprSrc x src'span
enExpr (StmtSrc stmt src'span) =
  ExprSrc (BlockExpr [StmtSrc stmt src'span]) src'span

stmtsExpr :: [StmtSrc] -> ExprSrc
stmtsExpr [] = ExprSrc (BlockExpr []) noSrcRange
stmtsExpr [s] = enExpr s
stmtsExpr stmts@(StmtSrc _stmt1 rng1 : rest) =
  ExprSrc (BlockExpr stmts) $ fullSpan rng1 rest
  where
    fullSpan :: SrcRange -> [StmtSrc] -> SrcRange
    fullSpan rng [] = rng
    fullSpan rng [StmtSrc _ (SrcRange _ final'end)] = rng {src'end = final'end}
    fullSpan rng (_ : more'stmts) = fullSpan rng more'stmts

-- Attribute reference
data AttrRef
  = ThisRef !SrcRange
  | ThatRef !SrcRange
  | SuperRef !SrcRange
  | DirectRef !AttrAddrSrc
  | IndirectRef !ExprSrc !AttrAddrSrc
  deriving (Eq)

instance Show AttrRef where
  show ThisRef {} = "this"
  show ThatRef {} = "that"
  show SuperRef {} = "super"
  show (DirectRef addr) = show addr
  show (IndirectRef owner addr) = show owner <> "." <> show addr

attrRefSpan :: AttrRef -> SrcRange
attrRefSpan (ThisRef !src'span) = src'span
attrRefSpan (ThatRef !src'span) = src'span
attrRefSpan (SuperRef !src'span) = src'span
attrRefSpan (DirectRef (AttrAddrSrc _ !src'span)) = src'span
attrRefSpan (IndirectRef (ExprSrc _ !tgt'span) (AttrAddrSrc _ !addr'span)) =
  SrcRange (src'start tgt'span) (src'end addr'span)

data AttrAddrSrc = AttrAddrSrc !AttrAddr !SrcRange
  deriving (Eq)

instance Show AttrAddrSrc where
  show (AttrAddrSrc addr _) = show addr

-- | the key to address attributes against a left hand object or current scope
data AttrAddr
  = -- | vanilla form, by alphanumeric name
    NamedAttr !AttrName
  | -- | static at-notation i.e. attribute name with arbitrary chars from a
    -- literal string
    QuaintAttr !Text
  | -- | dynamic at-notation i.e. get the symbol or string value from current
    -- scope, then use it to address an attribute
    SymbolicAttr !AttrName
  | -- | interpolated at-notation i.e. obtain a symbol value from arbitrary
    -- expression, then use it to address an attribute
    IntplSymAttr !Text !ExprSrc
  | -- | addressing attributes with a literal symbol value, usually being the
    -- result after `IntplSymAttr` interpolated
    LitSymAttr !Symbol
  | MissedAttrName
  | MissedAttrSymbol
  deriving (Eq)

instance Show AttrAddr where
  show = T.unpack . attrAddrStr

instance Hashable AttrAddr where
  hashWithSalt s (NamedAttr name) = s `hashWithSalt` name
  hashWithSalt s (QuaintAttr name) = s `hashWithSalt` name
  hashWithSalt s (SymbolicAttr sym) =
    s `hashWithSalt` ("@" :: Text) `hashWithSalt` sym
  hashWithSalt s (IntplSymAttr src _x) = s `hashWithSalt` src
  hashWithSalt s (LitSymAttr sym) = s `hashWithSalt` sym
  hashWithSalt s MissedAttrName = s `hashWithSalt` (101 :: Int)
  hashWithSalt s MissedAttrSymbol = s `hashWithSalt` (102 :: Int)

attrAddrStr :: AttrAddr -> Text
attrAddrStr (NamedAttr n) = n
attrAddrStr (QuaintAttr n) = T.pack ("@" <> show n)
attrAddrStr (SymbolicAttr s) = "@" <> s
attrAddrStr (IntplSymAttr src _x) = "@( " <> src <> " )"
attrAddrStr (LitSymAttr s) = symbolName s
attrAddrStr MissedAttrName = "<?>"
attrAddrStr MissedAttrSymbol = "@<?>"

receivesNamedArg :: Text -> ArgsReceiver -> Bool
receivesNamedArg !name (SingleReceiver !argRcvr) = case argRcvr of
  RecvArg (AttrAddrSrc !addr _) _ _ _ | addr == NamedAttr name -> True
  _ -> False
receivesNamedArg !name (PackReceiver !argRcvrs _) = hasNamedArg argRcvrs
  where
    hasNamedArg :: [ArgReceiver] -> Bool
    hasNamedArg [] = False
    hasNamedArg (arg : rest) = case arg of
      RecvArg (AttrAddrSrc !addr _) _ _ _ | addr == NamedAttr name -> True
      _ -> hasNamedArg rest
receivesNamedArg _ (WildReceiver _) = True
receivesNamedArg _ NullaryReceiver = False

data ArgsReceiver
  = PackReceiver ![ArgReceiver] !SrcRange
  | SingleReceiver !ArgReceiver
  | WildReceiver !SrcRange
  | NullaryReceiver
  deriving (Eq)

argsReceiverSpan :: ArgsReceiver -> SrcRange
argsReceiverSpan (PackReceiver _ src'span) = src'span
argsReceiverSpan (SingleReceiver ar) = argReceiverSpan ar
argsReceiverSpan (WildReceiver src'span) = src'span
argsReceiverSpan NullaryReceiver = noSrcRange

instance Show ArgsReceiver where
  show (PackReceiver rs _) = "( " ++ unwords ((++ ", ") . show <$> rs) ++ ")"
  show (SingleReceiver r) = "(" ++ show r ++ ")"
  show (WildReceiver _) = "*"
  show NullaryReceiver = "()"

data ArgReceiver
  = -- @* <ident>@
    RecvRestPosArgs !AttrAddrSrc
  | -- @** <ident>@
    RecvRestKwArgs !AttrAddrSrc
  | -- @*** <ident>@
    RecvRestPkArgs !AttrAddrSrc
  | -- @<ident> [: anno] [as some.other.attr] [= default'expr]@
    RecvArg !AttrAddrSrc !(Maybe InpAnno) !(Maybe AttrRef) !(Maybe ExprSrc)
  deriving (Eq, Show)

argReceiverSpan :: ArgReceiver -> SrcRange
argReceiverSpan (RecvRestPosArgs (AttrAddrSrc _ src'span)) = src'span
argReceiverSpan (RecvRestKwArgs (AttrAddrSrc _ src'span)) = src'span
argReceiverSpan (RecvRestPkArgs (AttrAddrSrc _ src'span)) = src'span
argReceiverSpan (RecvArg (AttrAddrSrc _ src'span) _ _ _) = src'span

data ArgsPacker = ArgsPacker [ArgSender] !SrcRange
  deriving (Eq)

instance Show ArgsPacker where
  show (ArgsPacker sndrs _) = show sndrs

data ArgSender
  = UnpackPosArgs !ExprSrc
  | UnpackKwArgs !ExprSrc
  | UnpackPkArgs !ExprSrc
  | SendPosArg !ExprSrc
  | SendKwArg !AttrAddrSrc !ExprSrc
  deriving (Eq, Show)

sentArgExprSrc :: ArgSender -> ExprSrc
sentArgExprSrc (UnpackPosArgs !x) = x
sentArgExprSrc (UnpackKwArgs !x) = x
sentArgExprSrc (UnpackPkArgs !x) = x
sentArgExprSrc (SendPosArg !x) = x
sentArgExprSrc (SendKwArg _ !x) = x

argSenderSpan :: ArgSender -> SrcRange
argSenderSpan !sndr = src'span
  where
    (ExprSrc _ !src'span) = sentArgExprSrc sndr

methodArrowArgsReceiver ::
  Expr ->
  (Either Text ArgsReceiver -> STM ()) ->
  STM ()
methodArrowArgsReceiver
  (AttrExpr (DirectRef argAttr@(AttrAddrSrc !addr _)))
  !exit = case addr of
    NamedAttr "_" -> exit $ Right $ SingleReceiver $ RecvRestPkArgs argAttr
    _ -> exit $ Right $ SingleReceiver $ RecvArg argAttr Nothing Nothing Nothing
methodArrowArgsReceiver (ArgsPackExpr (ArgsPacker !argSndrs !sndrsSpan)) !exit =
  cnvrt argSndrs []
  where
    cnvrt :: [ArgSender] -> [ArgReceiver] -> STM ()
    cnvrt [] !rcvrs = exit $ Right $ PackReceiver (reverse rcvrs) sndrsSpan
    cnvrt (sndr : rest) !rcvrs = case sndr of
      UnpackPosArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt rest (RecvRestPosArgs argRef : rcvrs)
      UnpackKwArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt rest (RecvRestKwArgs argRef : rcvrs)
      UnpackPkArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt rest (RecvRestPkArgs argRef : rcvrs)
      SendPosArg (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
        cnvrt rest (RecvArg argRef Nothing Nothing Nothing : rcvrs)
      SendKwArg !argRef !defExpr ->
        cnvrt rest (RecvArg argRef Nothing Nothing (Just defExpr) : rcvrs)
      !badSndr ->
        exit $
          Left $
            "invalid argument expr for arrow: " <> T.pack (show badSndr)
methodArrowArgsReceiver !badArgs !exit =
  exit $ Left $ "invalid argument expr for arrow: " <> T.pack (show badArgs)

producerArrowArgsReceiver ::
  Expr ->
  (Either Text ArgsReceiver -> STM ()) ->
  STM ()
producerArrowArgsReceiver (AttrExpr (DirectRef !argAttr)) !exit =
  exit $ Right $ SingleReceiver $ RecvArg argAttr Nothing Nothing Nothing
producerArrowArgsReceiver
  (ArgsPackExpr (ArgsPacker !argSndrs !sndrsSpan))
  !exit =
    cnvrt False argSndrs []
    where
      cnvrt :: Bool -> [ArgSender] -> [ArgReceiver] -> STM ()
      cnvrt !outletPrsnt [] !rcvrs =
        if outletPrsnt
          then exit $ Right $ PackReceiver (reverse rcvrs) sndrsSpan
          else
            exit $
              Right $
                PackReceiver
                  ( reverse
                      $! RecvArg
                        (AttrAddrSrc (NamedAttr "outlet") noSrcRange)
                        Nothing
                        ( Just
                            (DirectRef (AttrAddrSrc (NamedAttr "_") noSrcRange))
                        )
                        (Just (ExprSrc (LitExpr SinkCtor) noSrcRange)) :
                    rcvrs
                  )
                  sndrsSpan
      cnvrt !outletPrsnt (sndr : rest) !rcvrs = case sndr of
        UnpackPosArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
          cnvrt outletPrsnt rest (RecvRestPosArgs argRef : rcvrs)
        UnpackKwArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
          cnvrt outletPrsnt rest (RecvRestKwArgs argRef : rcvrs)
        UnpackPkArgs (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
          cnvrt outletPrsnt rest (RecvRestPkArgs argRef : rcvrs)
        SendPosArg (ExprSrc (AttrExpr (DirectRef !argRef)) _) ->
          cnvrt
            outletPrsnt
            rest
            (RecvArg argRef Nothing Nothing Nothing : rcvrs)
        SendKwArg argRef@(AttrAddrSrc !argAttr _) !defExpr ->
          cnvrt
            (outletPrsnt || argAttr == NamedAttr "outlet")
            rest
            (RecvArg argRef Nothing Nothing (Just defExpr) : rcvrs)
        !badSndr ->
          exit $
            Left $
              "invalid argument expr for arrow: " <> T.pack (show badSndr)
producerArrowArgsReceiver !badArgs !exit =
  exit $ Left $ "invalid argument expr for arrow: " <> T.pack (show badArgs)

-- | In-place annotation
--
-- Possibly for:
-- - a received argument's type
-- - a procedure's return type
-- - available effects expected by a class or procedure
data InpAnno
  = -- | Homogeneous collection annotation
    --
    -- The annotated artifact meant to be a postional-only apk (i.e. tuple) or
    -- list, containing hogeneous elements of the spoke type.
    --
    -- todo: represent the arity information? e.g.
    -- `*` for any number of elements, `+` for at least one element
    PluralAnno !InpAnno
  | -- | A constructor annotation
    --
    -- It's often a 'CallExpr' with ctor(***args) for construction prototyping,
    -- the call operation will be added by parser if omitted.
    --
    -- There are less cases for literal constructions, e.g. event `sink`.
    CtorProtoAnno !ExprSrc
  | -- | An arguments pack annotation
    --
    -- Each argument can optionally have its own respective annotation,
    -- positional-only arguments are designated with the underscore @_@ name.
    ApkProtoAnno !ArgsReceiver
  | -- | Procedure signature annotation
    --
    -- The procedure's arguments (each possibly annotated respectively) and
    -- return type annotation, positional-only arguments are designated with
    -- the underscore @_@ name.
    ProcSigAnno !ArgsReceiver !InpAnno
  | -- | Type string annotation
    --
    -- Single delimiter quoted literal string, interpreted as type name
    TypeStrAnno !Text
  | -- | Quaint annotation
    --
    -- Wide delimiter quoted literal string, content is not interpreted anyway.
    QuaintAnno !Text
  | -- | Alternate annotation
    --
    -- To express sum types
    AltAnno !InpAnno !InpAnno
  | -- | Effects expectations, with or without result type annotation
    EffsExpAnno ![EffArgAnno] !(Maybe InpAnno)
  deriving (Eq, Show)

-- | Specify an argument expected from dynamic scoping (i.e. effectful)
--
-- A default value can be specified, to state that it's not mandatory
data EffArgAnno
  = -- @<ident> [:anno] [= default'expr]@
    EffArgAnno !AttrAddrSrc !(Maybe InpAnno) !(Maybe ExprSrc)
  deriving (Eq, Show)

-- | Procedure declaration, result of parsing
data ProcDecl
  = HostDecl (ArgsPack -> EdhHostProc)
  | ProcDecl
      { edh'procedure'addr :: !AttrAddrSrc,
        edh'procedure'args :: !ArgsReceiver,
        edh'procedure'anno :: !(Maybe InpAnno),
        edh'procedure'body :: !StmtSrc,
        edh'procedure'loc :: !SrcLoc
      }

instance Eq ProcDecl where
  _ == _ = False

instance Show ProcDecl where
  show (HostDecl _) = "<host-proc>"
  show (ProcDecl (AttrAddrSrc !addr _) _ _ _ _) =
    "<edh-proc " <> T.unpack (attrAddrStr addr) <> ">"

procedureLoc :: ProcDecl -> SrcLoc
procedureLoc HostDecl {} = SrcLoc (SrcDoc "<host-world>") noSrcRange
procedureLoc pd@ProcDecl {} = edh'procedure'loc pd

procedureLoc' :: ProcDefi -> SrcLoc
procedureLoc' = procedureLoc . edh'procedure'decl

-- | Procedure definition, result of execution of the declaration
data ProcDefi = ProcDefi
  { edh'procedure'ident :: !Unique,
    edh'procedure'name :: !AttrKey,
    edh'procedure'lexi :: !Scope,
    edh'procedure'doc :: !OptDocCmt,
    edh'procedure'decl :: !ProcDecl
  }

instance Eq ProcDefi where
  ProcDefi x'u _ _ _ _ == ProcDefi y'u _ _ _ _ = x'u == y'u

instance Ord ProcDefi where
  compare (ProcDefi x'u _ _ _ _) (ProcDefi y'u _ _ _ _) = compare x'u y'u

instance Hashable ProcDefi where
  hashWithSalt s (ProcDefi !u _ _ _ _) = s `hashWithSalt` u

instance Show ProcDefi where
  show (ProcDefi _ !name _ _ (HostDecl _)) =
    T.unpack $ "<host-proc " <> attrKeyStr name <> ">"
  show (ProcDefi _ !name _ _ (ProcDecl (AttrAddrSrc !addr _) _ _ _ _)) =
    T.unpack $
      "<edh-proc "
        <> attrKeyStr name
        <> " : "
        <> attrAddrStr addr
        <> ">"

procedureName :: ProcDefi -> Text
procedureName !pd = case edh'procedure'name pd of
  AttrByName !n -> n
  AttrBySym (Symbol _ !r) -> r

-- | Expression definition
data ExprDefi = ExprDefi
  { edh'expr'ident :: !Unique,
    edh'expr'body :: !Expr,
    edh'expr'loc :: !SrcLoc
  }

instance Eq ExprDefi where
  ExprDefi x'u _ _ == ExprDefi y'u _ _ = x'u == y'u

instance Ord ExprDefi where
  compare (ExprDefi x'u _ _) (ExprDefi y'u _ _) = compare x'u y'u

instance Hashable ExprDefi where
  hashWithSalt s (ExprDefi !u _ _) = s `hashWithSalt` u

instance Show ExprDefi where
  show (ExprDefi _ _ loc) = "<expr @ " <> show loc <> ">"

data Prefix
  = PrefixPlus
  | PrefixMinus
  | Not
  | -- | to disregard the match target in context,
    -- for a branch condition
    Guard
  deriving (Eq, Show)

data DictKeyExpr
  = LitDictKey !Literal
  | AddrDictKey !AttrAddrSrc
  | ExprDictKey !ExprSrc -- this must be quoted in parenthesis
  deriving (Eq, Show)

data ExprSrc = ExprSrc !Expr !SrcRange
  deriving (Eq)

instance Show ExprSrc where
  show (ExprSrc x _) = "(" <> show x <> ")"

exprSrcSpan :: ExprSrc -> SrcRange
exprSrcSpan (ExprSrc _ !x'span) = x'span

exprSrcStart :: ExprSrc -> SrcPos
exprSrcStart (ExprSrc _ (SrcRange !start _end)) = start

exprSrcEnd :: ExprSrc -> SrcPos
exprSrcEnd (ExprSrc _ (SrcRange _start !end)) = end

data Expr
  = -- | the expr will be evaluated with result discarded,
    -- should always result in nil
    VoidExpr !ExprSrc
  | -- | symbol definition
    SymbolExpr !AttrName
  | -- | atomically isolated, mark an expression to be evaluated in a single
    -- STM transaction as a whole
    AtoIsoExpr !ExprSrc
  | LitExpr !Literal
  | PrefixExpr !Prefix !ExprSrc
  | IfExpr
      { if'condition :: !ExprSrc,
        if'consequence :: !StmtSrc,
        if'alternative :: !(Maybe StmtSrc)
      }
  | CaseExpr {case'target :: !ExprSrc, case'branches :: !ExprSrc}
  | -- note: the order of entries is reversed as parsed from source
    DictExpr ![(DictKeyExpr, ExprSrc)]
  | ListExpr ![ExprSrc]
  | ArgsPackExpr !ArgsPacker
  | ParenExpr !ExprSrc
  | -- | include a script into current scope's evaluation
    IncludeExpr !ExprSrc
  | -- | obtain the contents of a script as an expression value
    IncExprExpr !ExprSrc
  | -- | import with args (re)pack receiving syntax
    -- `into` a target object from specified expr, or current scope
    ImportExpr !ArgsReceiver !ExprSrc !(Maybe ExprSrc)
  | -- | only artifacts introduced within an `export` statement, into
    -- `this` object in context, are eligible for importing by others
    ExportExpr !ExprSrc
  | -- | namespace definition
    NamespaceExpr !ProcDecl !ArgsPacker
  | -- | class definition
    ClassExpr !ProcDecl
  | -- | method procedure definition
    MethodExpr !ProcDecl
  | -- | generator procedure definition
    GeneratorExpr !ProcDecl
  | -- | interpreter declaration, an interpreter procedure is not otherwise
    -- different from a method procedure, except it receives arguments
    -- in expression form rather than values, in addition to the reflective
    -- `callerScope` as first argument
    InterpreterExpr !ProcDecl
  | ProducerExpr !ProcDecl
  | -- | operator definition
    OpDefiExpr !OpFixity !Precedence !OpSymSrc !ProcDecl
  | -- | operator override
    OpOvrdExpr !OpFixity !Precedence !OpSymSrc !ProcDecl
  | BlockExpr ![StmtSrc]
  | ScopedBlockExpr ![StmtSrc]
  | YieldExpr !ExprSrc
  | -- | a for-from-do loop is made an expression in Edh, so it can
    -- appear as the right-hand expr of the comprehension (=<) operator.
    ForExpr
      { for'loop'scoped :: !Bool,
        for'loop'args :: !ArgsReceiver,
        for'loop'iter :: !ExprSrc,
        for'loop'body :: !StmtSrc
      }
  | -- | while loop
    WhileExpr !ExprSrc !StmtSrc
  | -- | do while loop
    DoWhileExpr !StmtSrc !ExprSrc
  | -- | effect calling out
    EffExpr !EffAddr
  | AttrExpr !AttrRef
  | IndexExpr
      { index'value :: !ExprSrc,
        index'target :: !ExprSrc
      }
  | CallExpr !ExprSrc !ArgsPacker
  | InfixExpr !OpSymSrc !ExprSrc !ExprSrc
  | -- specify a default by Edh code
    DefaultExpr !(Maybe ArgsPacker) !ExprSrc
  | -- to support interpolation within expressions, with source form
    ExprWithSrc !ExprSrc ![SourceSeg]
  | IntplExpr !ExprSrc
  deriving (Eq, Show)

data EffAddr
  = -- | call out an effectful artifact, search only outer stack frames,
    -- if from an effectful procedure run
    Perform !AttrAddrSrc
  | -- | call out an effectful artifact, always search full stack frames
    Behave !AttrAddrSrc
  | -- | call out a default effectful artifact, always search full stack frames
    Fallback !AttrAddrSrc
  deriving (Eq, Show)

data SourceSeg = SrcSeg !Text | IntplSeg !ExprSrc
  deriving (Eq, Show)

-- | Conversion formula from a source unit (named or arithmetic) to a named unit
data UnitFormula
  = -- | Converting from the source unit by multiplying a conversion factor
    RatioFormula !Decimal
  | -- | Converting from the source unit by evaluating an expression with
    -- the value in that unit bound to an attribute keyed by bracket symbol
    -- of that unit
    ExprFormula !ExprDefi !Text
  deriving (Eq)

instance Hashable UnitFormula where
  hashWithSalt s (RatioFormula r) =
    s `hashWithSalt` (-1 :: Int) `hashWithSalt` r
  hashWithSalt s (ExprFormula x _src) =
    s `hashWithSalt` (-2 :: Int) `hashWithSalt` x

-- | Defined unit of measure as 1st class value
--
-- The unit symbol here can never be empty. But the formulae map can contain a
-- formula from a 'NamedUnit' of empty identity (i.e. the dimensionless 1,
-- effectively unitless), indicating this named unit is effectively
-- dimensionless.
data NamedUnitDefi = NamedUnitDefi
  { uom'defi'doc :: !OptDocCmt,
    uom'defi'prim :: !Bool,
    uom'defi'sym :: !AttrName,
    -- | List of formulae convertible to this unit
    -- INVARIANT:
    --  - sorted by conversion factor, while arbitrary order at last if not a
    --    ratio factor, i.e. expr formulae always appear last
    --  - source unit specs are unique, overwriting cases should be exceptional
    --    but no errout by far in current implementation
    uom'defi'formulae :: ![(UnitSpec, UnitFormula)]
  }

instance Eq NamedUnitDefi where
  NamedUnitDefi _ _ x'sym _ == NamedUnitDefi _ _ y'sym _ =
    -- todo: should compare conversion formulae as well?
    -- mind to update hashing as well
    x'sym == y'sym

instance Show NamedUnitDefi where
  show (NamedUnitDefi _docCmt _prim sym _formulae) = T.unpack sym

instance Hashable NamedUnitDefi where
  hashWithSalt s (NamedUnitDefi _docCmt _prim sym _formulae) =
    -- todo: should hash conversion formulae as well?
    -- mind to update Eq instance as well
    s `hashWithSalt` sym -- `hashWithSalt` formulae

data UnitDefi
  = NamedUnitDefi' !NamedUnitDefi
  | ArithUnitDefi
      { uom'defi'numerators :: ![NamedUnitDefi],
        uom'defi'denominators :: ![NamedUnitDefi]
      }

uomReciprocal :: UnitDefi -> UnitDefi
uomReciprocal (NamedUnitDefi' u) = ArithUnitDefi [] [u]
uomReciprocal (ArithUnitDefi ns ds) = ArithUnitDefi ds ns

uomDefiIdent :: UnitDefi -> AttrName
uomDefiIdent (NamedUnitDefi' ud) = uom'defi'sym ud
uomDefiIdent (ArithUnitDefi ns []) =
  T.intercalate "*" (uom'defi'sym <$> ns)
uomDefiIdent (ArithUnitDefi ns ds) =
  T.intercalate "*" (uom'defi'sym <$> ns) <> "/"
    <> T.intercalate "/" (uom'defi'sym <$> ds)

isPrimaryUnit :: UnitDefi -> Bool
isPrimaryUnit (NamedUnitDefi' u) = uom'defi'prim u
isPrimaryUnit ArithUnitDefi {} = False

isUnitless :: UnitDefi -> Bool
isUnitless (NamedUnitDefi' u) = T.null $ uom'defi'sym u
isUnitless (ArithUnitDefi [] []) = True
isUnitless ArithUnitDefi {} = False

instance Eq UnitDefi where
  NamedUnitDefi' x == NamedUnitDefi' y = x == y
  ArithUnitDefi x'ns x'ds == ArithUnitDefi y'ns y'ds =
    x'ns == y'ns && x'ds == y'ds
  _ == _ = False

instance Show UnitDefi where
  show u = case uomDefiIdent u of
    "" -> "{# ① #}"
    uomIdent -> T.unpack uomIdent

instance Hashable UnitDefi where
  hashWithSalt s (NamedUnitDefi' d) =
    s `hashWithSalt` (-1 :: Int) `hashWithSalt` d
  hashWithSalt s (ArithUnitDefi ns ds) =
    s `hashWithSalt` (-2 :: Int) `hashWithSalt` ns `hashWithSalt` ds

data UnitDecl
  = -- | Declare a primary named unit
    PrimUnitDecl !AttrName !SrcRange
  | -- | Declare a conversion factor between a source unit and a named unit
    --
    -- Such two units have a common zero point, they are mutually convertible
    -- by just scaling.
    --
    -- Note bidirectional conversion is implied when rhs is a named unit.
    --
    -- See: https://en.wikipedia.org/wiki/Conversion_factor
    ConversionFactor !Decimal !AttrName !SrcRange !Decimal !UnitSpec
  | -- | Declare a one way conversion from a source unit to a named unit
    --
    -- Usually such two units don't have a common zero point, more
    -- sophisticated formula is thus needed.
    --
    -- E.g. https://en.wikipedia.org/wiki/Conversion_of_scales_of_temperature
    ConversionFormula !AttrName !SrcRange !ExprSrc !Text !AttrName
  deriving (Eq)

instance Show UnitDecl where
  show (PrimUnitDecl sym _) = T.unpack sym
  show (ConversionFactor nQty nSym _ dQty dUnit) =
    show nQty <> T.unpack nSym <> " = " <> show dQty <> show dUnit
  show (ConversionFormula outSym _ _formulaX fSrc _inUnit) =
    "[" <> T.unpack outSym <> "] = " <> T.unpack fSrc

-- | A quanty in some specified unit of measure
--
-- In case the uom is a 'NamedUnit' of empty symbol (i.e. dimensionless 1),
-- this quantity is equivalent to a pure number.
data Quantity = Quantity !Decimal !UnitDefi
  deriving (Eq)

instance Show Quantity where
  show (Quantity qty unit) = case D.showDecimal' qty of
    Left (n, d) -> case unit of
      NamedUnitDefi' u -> n <> show u <> "/" <> d
      ArithUnitDefi nus dus ->
        let ns = show <$> nus
            ds = show <$> dus
         in n <> intercalate "*" ns <> "/" <> d <> intercalate "*" ds
    Right s -> s <> show unit

instance Hashable Quantity where
  hashWithSalt s (Quantity qty unit) = s `hashWithSalt` qty `hashWithSalt` unit

-- | Unit of measure specification
--
-- Note the order of named units in an arithmetic unit matters, though multiple
-- occurrences of the same named unit will be moved together to the first
-- appearance place, as with the normalization process.
data UnitSpec
  = NamedUnit !AttrName !SrcRange
  | ArithUnit [(AttrName, SrcRange)] [(AttrName, SrcRange)]

instance Eq UnitSpec where
  NamedUnit x'sym _ == NamedUnit y'sym _ = x'sym == y'sym
  ArithUnit x'ns x'ds == ArithUnit y'ns y'ds =
    (fst <$> x'ns) == (fst <$> y'ns)
      && (fst <$> x'ds) == (fst <$> y'ds)
  _ == _ = False

-- | Normalize a UoM specification as one is parsed
uomNormalizeSpec :: UnitSpec -> UnitSpec
uomNormalizeSpec u@NamedUnit {} = u
uomNormalizeSpec (ArithUnit [(!uomSpec, !uomSpan)] []) =
  NamedUnit uomSpec uomSpan
uomNormalizeSpec (ArithUnit [] []) =
  NamedUnit "" noSrcRange -- dimensionless one (1)
uomNormalizeSpec (ArithUnit ns ds) =
  -- TODO: proper reductions
  ArithUnit ns ds

isUnitlessSpec :: UnitSpec -> Bool
isUnitlessSpec (NamedUnit sym _) = T.null sym
isUnitlessSpec ArithUnit {} = False

uomSpecIdent :: UnitSpec -> AttrName
uomSpecIdent (NamedUnit sym _) = sym
-- todo: render repeated named units in exponential form?
uomSpecIdent (ArithUnit nUnits []) =
  T.intercalate "*" (fst <$> nUnits)
uomSpecIdent (ArithUnit nUnits dUnits) =
  T.intercalate "*" (fst <$> nUnits) <> "/"
    <> T.intercalate "/" (fst <$> dUnits)

instance Show UnitSpec where
  show u = case uomSpecIdent u of
    "" -> "{# ① #}"
    uomIdent -> T.unpack uomIdent

instance Hashable UnitSpec where
  hashWithSalt s (NamedUnit sym _) =
    s `hashWithSalt` (-1 :: Int) `hashWithSalt` sym
  hashWithSalt s (ArithUnit nUnits dUnits) =
    s `hashWithSalt` (-2 :: Int) `hashWithSalt` (fst <$> nUnits)
      `hashWithSalt` (fst <$> dUnits)

data Literal
  = SinkCtor
  | NilLiteral
  | DecLiteral !Decimal
  | QtyLiteral !Decimal !UnitSpec
  | BoolLiteral !Bool
  | StringLiteral !Text
  | ValueLiteral !EdhValue
  deriving (Eq, Show)

instance Hashable Literal where
  hashWithSalt s SinkCtor = hashWithSalt s (-1 :: Int)
  hashWithSalt s NilLiteral = hashWithSalt s (0 :: Int)
  hashWithSalt s (DecLiteral x) = hashWithSalt s x
  hashWithSalt s (QtyLiteral qty uomSpec) =
    s `hashWithSalt` qty `hashWithSalt` uomSpec
  hashWithSalt s (BoolLiteral x) = hashWithSalt s x
  hashWithSalt s (StringLiteral x) = hashWithSalt s x
  hashWithSalt s (ValueLiteral x) = hashWithSalt s x

edhTypeNameOf :: EdhValue -> Text
edhTypeNameOf EdhNil = "nil"
edhTypeNameOf (EdhNamedValue n v) = n <> " := " <> edhTypeNameOf v
edhTypeNameOf EdhDecimal {} = "Decimal"
edhTypeNameOf EdhBool {} = "Bool"
edhTypeNameOf EdhBlob {} = "Blob"
edhTypeNameOf EdhString {} = "String"
edhTypeNameOf EdhSymbol {} = "Symbol"
edhTypeNameOf EdhUUID {} = "UUID"
edhTypeNameOf EdhRange {} = "Range"
edhTypeNameOf EdhPair {} = "Pair"
edhTypeNameOf EdhArgsPack {} = "ArgsPack"
edhTypeNameOf EdhDict {} = "Dict"
edhTypeNameOf EdhList {} = "List"
edhTypeNameOf (EdhObject o) = case edh'obj'store o of
  HashStore {} -> "Object"
  ClassStore !cls -> case edh'procedure'decl $ edh'class'proc cls of
    ProcDecl {} -> "Class"
    HostDecl {} -> "HostClass"
  HostStore (Dynamic tr _) -> "HostValue:" <> T.pack (show tr)
edhTypeNameOf (EdhProcedure pc _) = edhProcTypeNameOf pc
edhTypeNameOf (EdhBoundProc pc _ _ _) = edhProcTypeNameOf pc
edhTypeNameOf EdhBreak = "Break"
edhTypeNameOf EdhContinue = "Continue"
edhTypeNameOf EdhCaseClose {} = "CaseClose"
edhTypeNameOf EdhCaseOther = "CaseOther"
edhTypeNameOf EdhFallthrough = "Fallthrough"
edhTypeNameOf EdhRethrow = "Rethrow"
edhTypeNameOf EdhYield {} = "Yield"
edhTypeNameOf EdhReturn {} = "Return"
edhTypeNameOf EdhOrd {} = "Ord"
edhTypeNameOf EdhDefault {} = "Default"
edhTypeNameOf EdhSink {} = "Sink"
edhTypeNameOf EdhUoM {} = "UoM"
edhTypeNameOf EdhQty {} = "Qty"
edhTypeNameOf EdhExpr {} = "Expr"

edhProcTypeNameOf :: EdhProcDefi -> Text
edhProcTypeNameOf = \case
  EdhIntrOp {} -> "IntrinsicOperator"
  EdhOprtor _ _ _ !pd -> case edh'procedure'decl pd of
    HostDecl {} -> "HostOperator"
    ProcDecl {} -> "Operator"
  EdhMethod !pd -> case edh'procedure'decl pd of
    HostDecl {} -> "HostMethod"
    ProcDecl {} -> "Method"
  EdhGnrtor !pd -> case edh'procedure'decl pd of
    HostDecl {} -> "HostGenerator"
    ProcDecl {} -> "Generator"
  EdhIntrpr {} -> "Interpreter"
  EdhPrducr {} -> "Producer"
  EdhDescriptor {} -> "Descriptor"

objectScope :: Object -> STM Scope
objectScope !obj = case edh'obj'store obj of
  HostStore _ -> do
    -- provide the scope for a host object with an ad-hoc empty hash entity
    !hs <- iopdEmpty
    return
      Scope
        { edh'scope'entity = hs,
          edh'scope'this = obj,
          edh'scope'that = obj,
          edh'scope'proc = ocProc,
          edh'effects'stack = []
        }
  ClassStore (Class !cp !cs _ _) ->
    return
      Scope
        { edh'scope'entity = cs,
          edh'scope'this = obj,
          edh'scope'that = obj,
          edh'scope'proc = cp,
          edh'effects'stack = []
        }
  HashStore !hs ->
    let mustStr !v = case edhUltimate v of
          EdhString !s -> s
          _ -> error $ "bug: not a string - " <> show v
     in case procedureName ocProc of
          "module" -> do
            !moduName <-
              mustStr
                <$> iopdLookupDefault
                  (EdhString "<anonymous>")
                  (AttrByName "__name__")
                  hs
            !moduFile <-
              mustStr
                <$> iopdLookupDefault
                  (EdhString "<on-the-fly>")
                  (AttrByName "__file__")
                  hs
            return
              Scope
                { edh'scope'entity = hs,
                  edh'scope'this = obj,
                  edh'scope'that = obj,
                  edh'scope'proc =
                    ProcDefi
                      { edh'procedure'ident = edh'obj'ident obj,
                        edh'procedure'name =
                          AttrByName $ "module:" <> moduName,
                        edh'procedure'lexi = edh'procedure'lexi ocProc,
                        edh'procedure'doc = NoDocCmt,
                        edh'procedure'decl =
                          ProcDecl
                            { edh'procedure'addr =
                                AttrAddrSrc
                                  (NamedAttr $ "module:" <> moduName)
                                  zeroSrcRange,
                              edh'procedure'args = NullaryReceiver,
                              edh'procedure'anno = Nothing,
                              edh'procedure'body =
                                StmtSrc VoidStmt zeroSrcRange,
                              edh'procedure'loc =
                                SrcLoc (SrcDoc moduFile) zeroSrcRange
                            }
                      },
                  edh'effects'stack = []
                }
          _ ->
            return
              Scope
                { edh'scope'entity = hs,
                  edh'scope'this = obj,
                  edh'scope'that = obj,
                  edh'scope'proc = ocProc,
                  edh'effects'stack = []
                }
  where
    !oc = case edh'obj'store $ edh'obj'class obj of
      ClassStore !cls -> cls
      _ -> error "bug: class of an object not bearing ClassStore"
    ocProc = edh'class'proc oc

-- | Wrap any host value as an object
edhWrapHostValue :: Typeable t => EdhThreadState -> t -> STM Object
edhWrapHostValue !ets = edhWrapValue . toDyn
  where
    !world = edh'prog'world $ edh'thread'prog ets
    edhWrapValue = edh'value'wrapper world Nothing

-- | Wrap any host value as an object, with custom repr
edhWrapHostValue' :: Typeable t => EdhThreadState -> Text -> t -> STM Object
edhWrapHostValue' !ets !repr !v = edhWrapHostValue'' ets repr (toDyn v)

-- | Wrap any host value as an object, with custom repr
edhWrapHostValue'' :: EdhThreadState -> Text -> Dynamic -> STM Object
edhWrapHostValue'' !ets !repr = edhWrapValue
  where
    !world = edh'prog'world $ edh'thread'prog ets
    edhWrapValue = edh'value'wrapper world (Just repr)

-- | Create a reflective object capturing the specified scope as from the
-- specified context
--
-- todo currently only lexical context is recorded, the call frames may
--      be needed in the future
mkScopeWrapper :: EdhThreadState -> Scope -> STM Object
mkScopeWrapper !ets = edhWrapScope
  where
    !world = edh'prog'world $ edh'thread'prog ets
    edhWrapScope = edh'scope'wrapper world

data EdhIndex
  = EdhIndex !Int
  | EdhAny
  | EdhAll
  | EdhSlice
      { edh'slice'start :: !(Maybe Int),
        edh'slice'stop :: !(Maybe Int),
        edh'slice'step :: !(Maybe Int)
      }
  deriving (Eq)

mkHostProc ::
  Scope ->
  (ProcDefi -> EdhProcDefi) ->
  AttrName ->
  (ArgsPack -> EdhHostProc, ArgsReceiver) ->
  STM EdhValue
mkHostProc !scope !vc !nm (!p, _args) = do
  !u <- unsafeIOToSTM newUnique
  return $
    EdhProcedure
      ( vc
          ProcDefi
            { edh'procedure'ident = u,
              edh'procedure'name = AttrByName nm,
              edh'procedure'lexi = scope,
              edh'procedure'doc = NoDocCmt,
              edh'procedure'decl = HostDecl p
            }
      )
      Nothing

mkSymbolicHostProc ::
  Scope ->
  (ProcDefi -> EdhProcDefi) ->
  Symbol ->
  (ArgsPack -> EdhHostProc, ArgsReceiver) ->
  STM EdhValue
mkSymbolicHostProc !scope !vc !sym (!p, _args) = do
  !u <- unsafeIOToSTM newUnique
  return $
    EdhProcedure
      ( vc
          ProcDefi
            { edh'procedure'ident = u,
              edh'procedure'name = AttrBySym sym,
              edh'procedure'lexi = scope,
              edh'procedure'doc = NoDocCmt,
              edh'procedure'decl = HostDecl p
            }
      )
      Nothing

mkHostProperty ::
  Scope ->
  AttrName ->
  EdhHostProc ->
  Maybe (Maybe EdhValue -> EdhHostProc) ->
  STM EdhValue
mkHostProperty !scope !nm !getterProc !maybeSetterProc =
  mkHostProperty' scope (AttrByName nm) getterProc maybeSetterProc

mkHostProperty' ::
  Scope ->
  AttrKey ->
  EdhHostProc ->
  Maybe (Maybe EdhValue -> EdhHostProc) ->
  STM EdhValue
mkHostProperty' !scope !pk !getterProc !maybeSetterProc = do
  getter <- do
    u <- unsafeIOToSTM newUnique
    return $
      ProcDefi
        { edh'procedure'ident = u,
          edh'procedure'name = pk,
          edh'procedure'lexi = scope,
          edh'procedure'doc = NoDocCmt,
          edh'procedure'decl = HostDecl $ const getterProc
        }
  setter <- case maybeSetterProc of
    Nothing -> return Nothing
    Just !setterProc -> do
      u <- unsafeIOToSTM newUnique
      return $
        Just $
          ProcDefi
            { edh'procedure'ident = u,
              edh'procedure'name = pk,
              edh'procedure'lexi = scope,
              edh'procedure'doc = NoDocCmt,
              edh'procedure'decl = HostDecl $ \case
                ArgsPack [] _kwargs -> setterProc Nothing
                ArgsPack [tgtVal] _kwargs -> setterProc $ Just tgtVal
                _ -> \_exit _ets ->
                  throwSTM $
                    EdhHostError
                      EvalError
                      "bug: malformed call to getter"
                      (toDyn nil)
            }
  return $ EdhProcedure (EdhDescriptor getter setter) Nothing
