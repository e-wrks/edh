
-- | Edh Host Interface
--
-- With Haskell as the host language, Edh as the surface language,
-- this defines the interface for host code in Haskell to create
-- & control embedded Edh worlds, and to splice host (typically
-- side-effects free, i.e. pure, and fast-in-machine-speed)
-- functions, wrapped as host procedures, with procedures written
-- in Edh, those do arbitrary manipulations on arbitrary objects
-- in the world, but, less speedy as with interpreted execution.
module Language.Edh.EHI
  (
    -- * Exceptions
    EdhError(..)
  , ParserError
  , EdhCallFrame(..)
  , EdhCallContext(..)
  , EvalError(..)
  , UsageError(..)
  , edhKnownError

    -- * Event processing
  , EventSink(..)
  , newEventSink
  , subscribeEvents
  , publishEvent

    -- * STM/IO API for spliced interpreter

    -- ** Logging interface
  , EdhLogger
  , LogLevel
  , defaultEdhLogger

    -- ** Booting up
  , EdhWorld(..)
  , EdhRuntime(..)
  , createEdhWorld
  , installEdhBatteries
  , declareEdhOperators

    -- ** Spliced execution
  , bootEdhModule
  , createEdhModule
  , installEdhModule
  , importEdhModule
  , moduleContext
  , contextScope
  , parseEdhSource
  , evalEdhSource
  , evalEdhSource'
  , runEdhProgram
  , runEdhProgram'
  , viewAsEdhObject
  , createEdhObject
  , constructEdhObject
  , edhMakeCall
  , callEdhMethod
  , evalStmt
  , evalStmt'
  , evalBlock
  , evalCaseBlock
  , evalExpr
  , evalExprs
  , recvEdhArgs
  , packEdhExprs
  , packEdhArgs
  , OriginalValue(..)
  , EdhProg
  , EdhProgState(..)
  , EdhTxTask(..)
  , Context(..)
  , Scope(..)
  , EdhProcedure
  , EdhProcExit
  , runEdhProg
  , forkEdh
    -- ** Edh Runtime error
  , getEdhCallContext
  , throwEdh
  , throwEdhSTM
    -- ** CPS helpers
  , contEdhSTM
  , exitEdhSTM
  , exitEdhSTM'
  , exitEdhProc
  , exitEdhProc'
  , waitEdhSTM
  , edhWaitIO
  , edhNop
  , edhEndOfProc
    -- ** Reflective manipulation
  , StmtSrc(..)
  , Stmt(..)
  , Expr(..)
  , Prefix(..)
  , Literal(..)
  , AttrName
  , AttrAddr(..)
  , AttrAddressor(..)
  , ArgsReceiver(..)
  , ArgReceiver(..)
  , ArgsSender
  , ArgSender(..)
  , ProcDecl(..)
  , SourcePos(..)
  , sourcePosPretty
  , deParen

    -- ** Object system
  , Object(..)
  , Class
  , Entity(..)
  , EntityManipulater(..)
  , lookupEntityAttr
  , allEntityAttrs
  , changeEntityAttr
  , updateEntityAttrs
  , createMaoEntity
  , createHashEntity
  , createSideEntity
  , AttrKey(..)
  , attrKeyValue
  , lookupEdhCtxAttr
  , resolveEdhCtxAttr
  , lookupEdhObjAttr
  , lookupEdhSuperAttr
  , resolveEdhInstance
  , objectScope
  , mkScopeWrapper
  , wrappedScopeOf

    -- ** Value system
  , edhTypeOf
  , edhValueNull
  , edhValueRepr
  , EdhValue(..)
  , EdhTypeValue(..)
  , nil
  , edhNone
  , edhNothing
  , noneNil
  , true
  , false
  , nan
  , inf
  , D.Decimal(..)
  , Symbol(..)
  , Dict(..)
  , ItemKey
  , List(..)
  , ArgsPack(..)
  , ProcDefi(..)
  , EdhGenrCaller
  , mkSymbol
  , mkHostProc
  , mkHostClass
  , mkHostOper

    -- * args pack parsing
  , ArgsPackParser(..)
  , parseArgsPack

    -- * Monadic API for textual interpreter
  , runEdh
  , runEdhWithoutBatteries
  , runEdhShell
  , evalEdh
  , EdhShell
  , EdhBootstrap
  )
where

import           Prelude

import           Control.Exception
import           Control.Monad.Reader

import           Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

import           Text.Megaparsec

import qualified Data.Lossless.Decimal         as D

import           Language.Edh.Control
import           Language.Edh.Interpreter
import           Language.Edh.Batteries
import           Language.Edh.Runtime
import           Language.Edh.Event


evalEdh
  :: Text -- ^ source name
  -> Text -- ^ source code
  -> EdhShell (Either EdhError EdhValue) -- ^ eval result
evalEdh name code = do
  (world, modu) <- ask
  liftIO $ evalEdhSource world modu name code


runEdhShell
  :: ModuleId -- ^ shell module id
  -> EdhShell a -- ^ computation in an Edh shell
  -> EdhBootstrap (Either EdhError a) -- ^ final result
runEdhShell moduId (ReaderT f) = do
  world <- ask
  modu  <- createEdhModule world moduId "<adhoc>"
  liftIO $ tryJust Just $ f (world, modu)


runEdh :: MonadIO m => EdhBootstrap a -> EdhLogger -> m a
runEdh (ReaderT !f) !logger = liftIO $ do
  world <- createEdhWorld logger
  installEdhBatteries world
  f world

runEdhWithoutBatteries :: MonadIO m => EdhLogger -> EdhBootstrap a -> m a
runEdhWithoutBatteries !logger (ReaderT f) =
  liftIO $ createEdhWorld logger >>= f


type EdhShell a = ReaderT (EdhWorld, Object) IO a

type EdhBootstrap a = ReaderT EdhWorld IO a


data ArgsPackParser a = ArgsPackParser {
    pos'parsers :: [EdhValue -> a -> Either Text a]
    , kw'parsers :: Map.HashMap AttrName (EdhValue ->  a -> Either Text a)
  }
parseArgsPack :: a -> ArgsPackParser a -> ArgsPack -> Either Text a
parseArgsPack defVal (ArgsPackParser posParsers kwParsers) (ArgsPack posArgs kwArgs)
  = go posParsers kwParsers posArgs (Map.toList kwArgs) defVal
 where
  go
    :: [EdhValue -> a -> Either Text a]
    -> Map.HashMap AttrName (EdhValue -> a -> Either Text a)
    -> [EdhValue]
    -> [(AttrName, EdhValue)]
    -> a
    -> Either Text a
  go _  _    []      []                     result = Right result
  go [] _    (_ : _) _                      _      = Left "too many args"
  go _  kwps []      ((kwn, kwv) : kwargs') result = case Map.lookup kwn kwps of
    Nothing  -> Left $ "unknown arg: " <> kwn
    Just kwp -> kwp kwv result >>= go [] kwps [] kwargs'
  go (p : posParsers') kwps (arg : args') kwargs result =
    p arg result >>= go posParsers' kwps args' kwargs

