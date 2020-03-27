
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
  , EdhErrorTag(..)
  , ParserError
  , EdhCallFrame(..)
  , EdhCallContext(..)
  , edhKnownError

    -- * Event processing
  , EventSink(..)
  , newEventSink
  , subscribeEvents
  , publishEvent
  , forkEventProducer
  , forkEventConsumer
  , waitEventConsumer

    -- * STM/IO API for spliced interpreter

    -- ** Logging interface
  , EdhLogger
  , LogLevel
  , defaultEdhRuntime
  , defaultEdhIOLoop

    -- ** Booting up
  , EdhWorld(..)
  , EdhRuntime(..)
  , EdhConsoleIO(..)
  , createEdhWorld
  , installEdhBatteries
  , declareEdhOperators

    -- ** Spliced execution
  , runEdhModule
  , runEdhModule'
  , createEdhModule
  , installEdhModule
  , importEdhModule
  , moduleContext
  , contextScope
  , parseEdh
  , evalEdh
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
  , EdhProc
  , EdhProgState(..)
  , EdhTxTask(..)
  , Context(..)
  , Scope(..)
  , EdhProcedure
  , EdhProcExit
    -- ** Edh Runtime error
  , getEdhCallContext
  , edhThrow
  , edhCatch
  , throwEdh
  , throwEdhSTM
    -- ** CPS helpers
  , runEdhProc
  , contEdhSTM
  , exitEdhSTM
  , exitEdhSTM'
  , exitEdhProc
  , exitEdhProc'
  , seqcontSTM
  , mapcontSTM
    -- ** Sync utilities
  , forkEdh
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
  , EdhHostCtor
  , mkHostClass
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
  , edhTypeNameOf
  , edhTypeOf
  , edhValueNull
  , edhValueRepr
  , EdhValue(..)
  , EdhTypeValue(..)
  , edhUltimate
  , edhExpr
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
  , mkIntrinsicOp

    -- * args pack parsing
  , ArgsPackParser(..)
  , parseArgsPack
  )
where

import           Prelude

import           Control.Concurrent.STM

import           Text.Megaparsec

import qualified Data.Lossless.Decimal         as D

import           Language.Edh.Control
import           Language.Edh.Batteries
import           Language.Edh.Runtime
import           Language.Edh.Event
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.PkgMan
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.Evaluate


seqcontSTM :: forall a . [(a -> STM ()) -> STM ()] -> ([a] -> STM ()) -> STM ()
seqcontSTM !xs !exit = go xs []
 where
  go :: [(a -> STM ()) -> STM ()] -> [a] -> STM ()
  go []         ys = exit $! reverse $! ys
  go (x : rest) ys = x $ \y -> go rest (y : ys)

mapcontSTM
  :: forall a b
   . (a -> b)
  -> [(a -> STM ()) -> STM ()]
  -> [(b -> STM ()) -> STM ()]
mapcontSTM !f !xs = go xs []
 where
  go
    :: [(a -> STM ()) -> STM ()]
    -> [(b -> STM ()) -> STM ()]
    -> [(b -> STM ()) -> STM ()]
  go []         ys = reverse $! ys
  go (x : rest) ys = go rest (y : ys) where y b = x (\a -> b (f a))
