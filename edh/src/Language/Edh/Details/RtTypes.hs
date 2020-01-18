
module Language.Edh.Details.RtTypes where

import           Prelude

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Exception
import           Control.Monad.Except
import           Control.Monad.Reader

import           Control.Concurrent.STM

import           Data.Foldable
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.Map.Strict               as Map
import           Data.List.NonEmpty             ( NonEmpty(..) )
import qualified Data.List.NonEmpty            as NE

import           Foreign.C.String
import           Foreign.Marshal.Alloc
import           System.Mem.Weak
import           System.IO.Unsafe

import           Text.Megaparsec

import           Data.Lossless.Decimal         as D

import           Language.Edh.Control
import           Language.Edh.AST


-- | A dict in Edh is neither an object nor an entity, but just a
-- mutable associative map.
--
-- A dict has items associated by 'ItemKey'.
newtype Dict = Dict (TVar DictStore)
  deriving (Eq)
type DictStore = Map.Map ItemKey EdhValue
instance Show Dict where
  show (Dict d) = showEdhDict ds where ds = unsafePerformIO $ readTVarIO d
data ItemKey = ItemByType !EdhTypeValue
    | ItemByStr !Text | ItemBySym !Symbol
    | ItemByNum !Decimal | ItemByBool !Bool
  deriving (Eq, Ord)
instance Show ItemKey where
  show (ItemByType k) = show k
  show (ItemByStr  k) = show k
  show (ItemBySym  k) = show k
  show (ItemByNum  k) = showDecimal k
  show (ItemByBool k) = show $ EdhBool k

showEdhDict :: DictStore -> String
showEdhDict ds = if Map.null ds
  then "{,}" -- make it obvious this is an empty dict
  else -- advocate trailing comma here
    "{ "
    ++ concat [ show k ++ ":" ++ show v ++ ", " | (k, v) <- Map.toList ds ]
    ++ "}"

itemKeyValue :: ItemKey -> EdhValue
itemKeyValue (ItemByType tyv) = EdhType tyv
itemKeyValue (ItemByStr  s  ) = EdhString s
itemKeyValue (ItemBySym  s  ) = EdhSymbol s
itemKeyValue (ItemByNum  d  ) = EdhDecimal d
itemKeyValue (ItemByBool b  ) = EdhBool b

toPairList :: DictStore -> [EdhValue]
toPairList d = (<$> Map.toList d) $ \(k, v) -> EdhPair (itemKeyValue k) v

edhDictFromEntity :: Entity -> STM Dict
edhDictFromEntity ent = do
  em <- readTVar ent
  (Dict <$>) $ newTVar $ Map.fromAscList
    [ (keyAttr2Item k, v) | (k, v) <- Map.toAscList em ]
 where
  keyAttr2Item :: AttrKey -> ItemKey
  keyAttr2Item (AttrByName nm ) = ItemByStr nm
  keyAttr2Item (AttrBySym  sym) = ItemBySym sym

-- | An entity in Edh is the backing storage for a scope, with possibly 
-- an object mounted to it with one class and many supers
--
-- An entity has attributes associated by 'AttrKey'.
type Entity = TVar EntityStore
type EntityStore = Map.Map AttrKey EdhValue
data AttrKey = AttrByName !AttrName | AttrBySym !Symbol
    deriving (Eq, Ord, Show)

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
--
-- Note: we rely on the 'Ord' instance of 'CString' field (which is
--       essentially a ptr), for trivial implementation of 'Symbol'
--       's 'Ord' instance, so it can be used as attribute key on an
--       entity (the underlying 'Map.Map' storage per se).
newtype Symbol = Symbol {
    symbol'description :: CString
  } deriving (Eq, Ord)
instance Show Symbol where
  show (Symbol dp) = "<@" <> sd <> ">"
    where sd = unsafePerformIO $ peekCString dp
mkSymbol :: String -> STM Symbol
mkSymbol !d = unsafeIOToSTM $ do
  !s <- newCString d
  let !sym = Symbol s
  addFinalizer sym $ free s
  return sym


-- | A list in Edh is a multable, singly-linked, prepend list.
newtype List = List (TVar [EdhValue])
  deriving (Eq)
instance Show List where
  show (List l) = if null ll
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
    -- | the lexical context in which the executing procedure is defined
    , lexiStack :: ![Scope]
    -- | the Edh procedure holding this scope
    , scopeProc :: !ProcDecl
  }
instance Eq Scope where
  Scope x'e _ _ _ _ == Scope y'e _ _ _ _ = x'e == y'e
instance Show Scope where
  show (Scope _ _ _ _ (ProcDecl pName argsRcvr (StmtSrc (!srcPos, _)))) =
    "<"
      ++ T.unpack pName
      ++ show argsRcvr
      ++ " @ "
      ++ sourcePosPretty srcPos
      ++ ">"


-- | An object views an entity, with inheritance relationship 
-- to any number of super objects.
data Object = Object {
    -- | the entity stores attribute set of the object
    objEntity :: !Entity
    -- | the class (a.k.a constructor) procedure of the object
    , objClass :: !Class
    -- | up-links for object inheritance hierarchy
    , objSupers :: !(TVar [Object])
  }
instance Eq Object where
  -- equality by pointer to entity
  Object x'e _ _ == Object y'e _ _ = x'e == y'e
instance Show Object where
  -- it's not right to call 'atomically' here to read 'objSupers' for
  -- the show, as 'show' may be called from an stm transaction, stm
  -- will fail hard on encountering of nested 'atomically' calls.
  show (Object _ (Class _ (ProcDecl cn _ _)) _) =
    "<object: " ++ T.unpack cn ++ ">"

-- | View an entity as object of specified class with specified ancestors
-- this is the black magic you want to avoid
viewAsEdhObject :: Entity -> Class -> [Object] -> STM Object
viewAsEdhObject ent cls supers = Object ent cls <$> newTVar supers

data Class = Class {
    -- | the lexical context where this class procedure is defined
    classLexiStack :: !(NonEmpty Scope)
    , classProcedure :: !ProcDecl
  }
instance Eq Class where
  Class x's x'pd == Class y's y'pd = x's == y's && x'pd == y'pd
instance Show Class where
  show (Class _ (ProcDecl cn _ _)) = "<class: " ++ T.unpack cn ++ ">"

data Method = Method {
    methodLexiStack :: !(NonEmpty Scope)
    , methodProcedure :: !ProcDecl
  } deriving (Eq)
instance Show Method where
  show (Method _ (ProcDecl mn _ _)) = "<method: " ++ T.unpack mn ++ ">"

data GenrDef = GenrDef {
    generatorLexiStack :: !(NonEmpty Scope)
    , generatorProcedure :: !ProcDecl
  } deriving (Eq)
instance Show GenrDef where
  show (GenrDef _ (ProcDecl mn _ _)) = "<generator: " ++ T.unpack mn ++ ">"

data Interpreter = Interpreter {
    interpreterLexiStack :: !(NonEmpty Scope)
    , interpreterProcedure :: !ProcDecl
  } deriving (Eq)
instance Show Interpreter where
  show (Interpreter _ (ProcDecl mn _ _)) =
    "<interpreter: " ++ T.unpack mn ++ ">"

data Operator = Operator {
    operatorLexiStack :: !(NonEmpty Scope)
    , operatorProcedure :: !ProcDecl
    -- the overridden operator procedure
    , operatorPredecessor :: !(Maybe EdhValue)
    -- todo this is some redundant, as the precedences are always available
    -- from 'worldOperators', but being an 'MVar' that's non-trivial to read
    -- safely from a pure 'show' function. can remove this field once we
    -- switched to a better introspection tool for operators at runtime.
    , operatorPrecedence :: !Precedence
  } deriving (Eq)
instance Show Operator where
  show (Operator _ (ProcDecl opSym _ _) _ prec) =
    "<operator: (" ++ T.unpack opSym ++ ") " ++ show prec ++ ">"


-- | A world for Edh programs to change
data EdhWorld = EdhWorld {
    -- | root object of this world
    worldRoot :: !Object
    -- | all module objects in this world belong to this class
    , moduleClass :: !Class
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
    , worldModules :: !(TMVar (Map.Map ModuleId (TMVar EdhValue)))
    -- | interface to the embedding host runtime
    , worldRuntime :: !(TMVar EdhRuntime)
  }
instance Eq EdhWorld where
  EdhWorld x'root _ _ _ _ _ == EdhWorld y'root _ _ _ _ _ = x'root == y'root

data EdhRuntime = EdhRuntime {
  runtimeLogger :: !EdhLogger
  , runtimeLogLevel :: !LogLevel
  }
type EdhLogger = LogLevel -> Maybe String -> ArgsPack -> STM ()
type LogLevel = Int


-- | The ultimate nothingness (Chinese 无极/無極), i.e. <nothing> out of <chaos>
wuji :: EdhProgState -> OriginalValue
wuji !pgs = OriginalValue nil worldScope root
 where
  !worldScope = NE.head $ classLexiStack $ objClass root
  !root       = worldRoot world
  !world      = contextWorld $ edh'context pgs
{-# INLINE wuji #-}


-- | The monad for running of an Edh program
type EdhProg = ReaderT EdhProgState STM

-- | The states of a program
data EdhProgState = EdhProgState {
    edh'fork'queue :: !(TQueue EdhTxTask)
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
    writeTQueue (edh'fork'queue pgs)
      $ EdhTxTask pgs False (wuji pgs) (const prog)
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

-- | An atomic task, an Edh program is composed form many this kind of tasks.
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
  let !ctx               = edh'context pgs
      (StmtSrc (!sp, _)) = contextStmt ctx
      !frames            = foldl'
        (\sfs (Scope _ _ _ _ (ProcDecl procName _ (StmtSrc (spos, _)))) ->
          (procName, T.pack (sourcePosPretty spos)) : sfs
        )
        []
        ( takeWhile (\(Scope _ _ _ lexi'stack _) -> not (null lexi'stack))
        $ NE.toList (callStack ctx)
        )
  in  EdhErrorContext msg (T.pack $ sourcePosPretty sp) frames

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
    , keyword'args :: !(Map.Map AttrName EdhValue)
  } deriving (Eq)
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
--
-- Note: we rely on the 'CString' field (which is essentially a ptr),
--       for equality testing of host procedures.
data HostProcedure = HostProcedure {
    hostProc'name :: !CString
    , hostProc'proc :: !EdhProcedure
  }
instance Eq HostProcedure where
  HostProcedure x'n _ == HostProcedure y'n _ = x'n == y'n
instance Show HostProcedure where
  show (HostProcedure pn _) = "<hostproc: " ++ nm ++ ">"
    where nm = unsafePerformIO $ peekCString pn

hostProcDecl :: CString -> STM ProcDecl
hostProcDecl !pn = do
  nm <- unsafeIOToSTM $ peekCString pn
  return ProcDecl
    { procedure'name = T.pack nm
    , procedure'args = WildReceiver
    , procedure'body = StmtSrc
                         ( SourcePos { sourceName   = "<hostcode>"
                                     , sourceLine   = mkPos 1
                                     , sourceColumn = mkPos 1
                                     }
                         , VoidStmt
                         )
    }


-- | An event sink is similar to a Go channel, but is broadcast
-- in nature, in contrast to the unicast nature of channels in Go.
data EventSink = EventSink {
    -- | sequence number, increased on every new event posting.
    -- must read zero when no event has ever been posted to this sink,
    -- non-zero otherwise. monotonicly increasing most of the time,
    -- but allowed to wrap back to 1 when exceeded 'maxBound::Int'
    -- negative values can be used to indicate abnormal conditions.
    evs'seqn :: !(TVar Int)
    -- | most recent value, not valid until evs'seqn turns non-zero
    , evs'mrv :: !(TVar EdhValue)
    -- | the broadcast channel
    , evs'chan :: !(TChan EdhValue)
  } deriving Eq
instance Show EventSink where
  show (EventSink _ _ _) = "<sink>"


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
  -- * end values (immutable)
    | EdhNil
    | EdhDecimal !Decimal
    | EdhBool !Bool
    | EdhString !Text
    | EdhSymbol !Symbol

  -- * direct pointer (to entities) values
    | EdhObject !Object

  -- * mutable containers
    | EdhDict !Dict
    | EdhList !List

  -- * immutable containers
  --   the elements may still pointer to mutable data
    | EdhPair !EdhValue !EdhValue
    | EdhTuple ![EdhValue]
    | EdhArgsPack ArgsPack

  -- * host procedures callable from Edh world
    | EdhHostProc !HostProcedure
    | EdhHostOper !Precedence !HostProcedure
    | EdhHostGenr !HostProcedure

  -- * precedures defined by Edh code
    | EdhClass !Class
    | EdhMethod !Method
    | EdhOperator !Operator
    | EdhGenrDef !GenrDef
    | EdhInterpreter !Interpreter

  -- * flow control
    | EdhBreak
    | EdhContinue
    | EdhCaseClose !EdhValue
    | EdhFallthrough
    | EdhYield !EdhValue
    | EdhReturn !EdhValue

  -- * event sink
    | EdhSink !EventSink

  -- * reflection
    | EdhExpr !Expr

edhValueStr :: EdhValue -> Text
edhValueStr (EdhString s) = s
edhValueStr v             = T.pack $ show v

edhValueNull :: EdhValue -> STM Bool
edhValueNull EdhNil                = return True
edhValueNull (EdhDecimal d       ) = return $ D.decimalIsNaN d || d == 0
edhValueNull (EdhBool    b       ) = return $ b == False
edhValueNull (EdhString  s       ) = return $ T.null s
edhValueNull (EdhDict    (Dict d)) = Map.null <$> readTVar d
edhValueNull (EdhList    (List l)) = null <$> readTVar l
edhValueNull (EdhTuple   l       ) = return $ null l
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
  show (EdhHostOper prec (HostProcedure pn _)) =
    "<hostop: (" ++ nm ++ ") " ++ show prec ++ ">"
    where nm = unsafePerformIO $ peekCString pn
  show (EdhHostGenr (HostProcedure pn _)) = "<hostgen: " ++ nm ++ ">"
    where nm = unsafePerformIO $ peekCString pn


  show (EdhClass       v) = show v
  show (EdhMethod      v) = show v
  show (EdhOperator    v) = show v
  show (EdhGenrDef     v) = show v
  show (EdhInterpreter v) = show v

  show EdhBreak           = "<break>"
  show EdhContinue        = "<continue>"
  show (EdhCaseClose v)   = "<caseclose: " ++ show v ++ ">"
  show EdhFallthrough     = "<fallthrough>"
  show (EdhYield  v)      = "<yield: " ++ show v ++ ">"
  show (EdhReturn v)      = "<return: " ++ show v ++ ">"

  show (EdhSink   v)      = show v

  show (EdhExpr   v)      = "<expr: " ++ show v ++ ">"

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
  EdhHostGenr    x     == EdhHostGenr    y     = x == y

  EdhClass       x     == EdhClass       y     = x == y
  EdhMethod      x     == EdhMethod      y     = x == y
  EdhOperator    x     == EdhOperator    y     = x == y
  EdhGenrDef     x     == EdhGenrDef     y     = x == y
  EdhInterpreter x     == EdhInterpreter y     = x == y

  EdhBreak             == EdhBreak             = True
  EdhContinue          == EdhContinue          = True
  EdhCaseClose x       == EdhCaseClose y       = x == y
  EdhFallthrough       == EdhFallthrough       = True
-- todo: regard a yielded/returned value equal to the value itself ?
  EdhYield  x'v        == EdhYield  y'v        = x'v == y'v
  EdhReturn x'v        == EdhReturn y'v        = x'v == y'v

  EdhSink   x          == EdhSink   y          = x == y

  EdhExpr   x'v        == EdhExpr   y'v        = x'v == y'v

-- todo: support coercing equality ?
--       * without this, we are a strongly typed dynamic language
--       * with this, we'll be a weakly typed dynamic language
  _                    == _                    = False


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


edhTypeOf :: EdhValue -> EdhValue
edhTypeOf (EdhType _)        = EdhType TypeType

edhTypeOf EdhNil             = nil
edhTypeOf (EdhDecimal _    ) = EdhType DecimalType
edhTypeOf (EdhBool    _    ) = EdhType BoolType
edhTypeOf (EdhString  _    ) = EdhType StringType
edhTypeOf (EdhSymbol  _    ) = EdhType SymbolType
edhTypeOf (EdhObject  _    ) = EdhType ObjectType
edhTypeOf (EdhDict    _    ) = EdhType DictType
edhTypeOf (EdhList    _    ) = EdhType ListType
edhTypeOf (EdhPair _ _     ) = EdhType PairType
edhTypeOf (EdhTuple    _   ) = EdhType TupleType
edhTypeOf (EdhArgsPack _   ) = EdhType ArgsPackType
edhTypeOf (EdhHostProc _   ) = EdhType HostProcType
edhTypeOf (EdhHostOper _ _ ) = EdhType HostOperType
edhTypeOf (EdhHostGenr    _) = EdhType HostGenrType
edhTypeOf (EdhClass       _) = EdhType ClassType
edhTypeOf (EdhMethod      _) = EdhType MethodType
edhTypeOf (EdhOperator    _) = EdhType OperatorType
edhTypeOf (EdhGenrDef     _) = EdhType GeneratorType
edhTypeOf (EdhInterpreter _) = EdhType InterpreterType
edhTypeOf EdhBreak           = EdhType BreakType
edhTypeOf EdhContinue        = EdhType ContinueType
edhTypeOf (EdhCaseClose _)   = EdhType CaseCloseType
edhTypeOf EdhFallthrough     = EdhType FallthroughType
edhTypeOf (EdhYield  _)      = EdhType YieldType
edhTypeOf (EdhReturn _)      = EdhType ReturnType
edhTypeOf (EdhSink   _)      = EdhType SinkType
edhTypeOf (EdhExpr   _)      = EdhType ExprType


