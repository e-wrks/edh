
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
    InterpretError(..)
  , ParserError
  , EdhErrorContext(..)
  , EvalError(..)
  , UsageError(..)
  , edhKnownError

    -- * STM/IO API for Edh/RT to be used as a spliced interpreter

    -- ** Logging interface
  , EdhLogger
  , LogLevel
  , defaultEdhLogger

    -- ** Bootstrapping
  , EdhWorld(..)
  , EdhRuntime(..)
  , createEdhWorld
  , installEdhBatteries
  , declareEdhOperators
  , installEdhAttrs
  , installEdhAttr

    -- ** Calling Edh from Haskell
  , bootEdhModule
  , createEdhModule
  , moduleContext
  , contextScope
  , evalEdhSource
  , runEdhProgram
  , runEdhProgram'
  , constructEdhObject
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
  , edhNop
    -- ** AST manipulation
  , module AST
  , SourcePos(..)
  , sourcePosPretty
  , deParen
  , deBlock

    -- ** Object system
  , lookupEdhCtxAttr
  , lookupEdhObjAttr
  , resolveEdhCtxAttr
  , resolveEdhObjAttr
  , resolveEdhInstance
  , mkScopeWrapper

    -- ** Value system
  , edhTypeOf
  , edhValueStr
  , edhValueNull
  , EdhValue(..)
  , nil
  , true
  , false
  , nan
  , inf
  , D.Decimal(..)
  , Symbol(..)
  , Entity
  , AttrKey(..)
  , Dict(..)
  , ItemKey(..)
  , List(..)
  , ArgsPack(..)
  , Object(..)
  , HostProcedure(..)
  , EdhGenrCaller
  , Class(..)
  , Method(..)
  , Operator(..)
  , GenrDef(..)
  , Interpreter(..)
  , mkSymbol
  , mkHostProc
  , mkHostOper

    -- * Event processing
  , EventSink(..)
  , newEventSink
  , subscribeEvents
  , publishEvent

    -- * Monadic API for Edh/RT to be used as a textual interpreter
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
import           Language.Edh.AST              as AST


evalEdh
  :: Text -- ^ Edh code
  -> EdhShell (Either InterpretError EdhValue) -- ^ eval result
evalEdh code = do
  (world, modu) <- ask
  liftIO $ evalEdhSource world modu code


runEdhShell
  :: ModuleId -- ^ shell module id
  -> EdhShell a -- ^ computation in an Edh shell
  -> EdhBootstrap (Either InterpretError a) -- ^ final result
runEdhShell moduId (ReaderT f) = do
  world <- ask
  modu  <- createEdhModule world moduId
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

