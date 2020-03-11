
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
  , EdhErrorContext(..)
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
  , installEdhAttrs
  , installEdhAttr

    -- ** Spliced execution
  , bootEdhModule
  , createEdhModule
  , installEdhModule
  , importEdhModule
  , moduleContext
  , contextScope
  , parseEdhSource
  , evalEdhSource
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
  , packHostProcArgs
  , runEdhProg
  , forkEdh
    -- ** Edh Runtime error
  , getEdhErrorContext
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
  , AttrAddr(..)
  , ArgsReceiver(..)
  , ArgReceiver(..)
  , ArgsSender
  , ArgSender(..)
  , ProcDecl(..)
  , SourcePos(..)
  , sourcePosPretty
  , deParen
  , deBlock

    -- ** Object system
  , Object(..)
  , Class
  , Entity(..)
  , EntityStore(..)
  , createEntity
  , maoEntityStore
  , hashEntityStore
  , constEntityStore
  , AttrKey(..)
  , attrKeyValue
  , lookupEdhCtxAttr
  , lookupEdhObjAttr
  , lookupEdhSuperAttr
  , resolveEdhCtxAttr
  , resolveEdhObjAttr
  , resolveEdhSuperAttr
  , resolveEdhInstance
  , objectScope
  , mkScopeWrapper
  , wrappedScopeOf

    -- ** Value system
  , edhTypeOf
  , edhValueStr
  , edhValueNull
  , EdhValue(..)
  , EdhTypeValue(..)
  , nil
  , edhNone
  , edhNothing
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
  , mkHostOper

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

import           Text.Megaparsec

import qualified Data.Lossless.Decimal         as D

import           Language.Edh.Control
import           Language.Edh.Interpreter
import           Language.Edh.Batteries
import           Language.Edh.Runtime
import           Language.Edh.Event


evalEdh
  :: Text -- ^ Edh code
  -> EdhShell (Either EdhError EdhValue) -- ^ eval result
evalEdh code = do
  (world, modu) <- ask
  liftIO $ evalEdhSource world modu code


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

