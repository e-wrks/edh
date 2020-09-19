{-# LANGUAGE PatternSynonyms #-}

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

    -- ** Console interface w/ a default implementation
  , EdhConsole(..)
  , EdhConsoleIO(..)
  , EdhLogger
  , LogLevel
  , defaultEdhConsole
  , defaultEdhConsoleSettings

    -- ** World bootstraping
  , EdhWorld(..)
  , createEdhWorld
  , worldContext
  , installEdhBatteries
  , declareEdhOperators

    -- ** Spliced execution
  , performEdhEffect
  , performEdhEffect'
  , behaveEdhEffect
  , behaveEdhEffect'
  , runEdhModule
  , runEdhModule'
  , runEdhFile
  , runEdhFile'
  , EdhModulePreparation
  , edhModuleAsIs
  , createEdhModule
  , installEdhModule
  , installedEdhModule
  , importEdhModule
  , moduleContext
  , contextScope
  , contextFrame
  , parseEdh
  , parseEdh'
  , evalEdh
  , evalEdh'
  , haltEdhProgram
  , runEdhProgram
  , runEdhProgram'
  , edhPrepareCall
  , edhPrepareCall'
  , callEdhMethod
  , evalStmt
  , evalStmt'
  , evalExpr
  , evalExprs
  , recvEdhArgs
  , packEdhExprs
  , packEdhArgs
  , implantEffect
  , implantEffects
  , EdhTx
  , EdhThreadState(..)
  , EdhTask(..)
  , Context(..)
  , Scope(..)
  , EdhProc(..)
  , EdhHostProc
  , EdhTxExit
    -- ** Edh Runtime error
  , getEdhCallContext
  , edhCreateError
  , edhThrow
  , edhCatch
  , throwEdh
  , edhThrowTx
  , edhCatchTx
  , throwEdhTx
    -- ** CPS helpers
  , exitEdh
  , runEdhTx
  , exitEdhTx
  , seqcontSTM
  , foldcontSTM
  , mapcontSTM
    -- ** Sync utilities
  , edhDoSTM
  , endOfEdh
  , forkEdh
  , edhContSTM
  , edhContIO
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
  , ArgsPacker
  , ArgSender(..)
  , ProcDecl(..)
  , procedureName
  , SourcePos(..)
  , mkPos
  , sourcePosPretty

    -- ** Object system
  , Object(..)
  , ObjectStore(..)
  , castObjectStore
  , castObjectStore'
  , castObjSelfStore
  , castObjSelfStore'
  , withThisHostObj
  , withThisHostObj'
  , withHostObject
  , withHostObject'
  , withDerivedHostObject
  , withDerivedHostObject'
  , EdhObjectAllocator
  , Class
  , edhClassName
  , objClassName
  , edhCreateHostObj
  , edhCreateObj
  , edhConstructObj
  , edhMutCloneObj
  , edhCloneHostObj
  , EntityStore
  , AttrKey(..)
  , attrKeyStr
  , attrKeyValue
  , lookupEdhCtxAttr
  , resolveEdhCtxAttr
  , lookupEdhObjAttr
  , lookupEdhObjMagic
  , lookupEdhSuperAttr
  , resolveEdhInstance
  , objectScope
  , mkScopeWrapper

    -- ** Value system
  , edhSetValue
  , createEdhDict
  , setDictItem
  , dictEntryList
  , edhTypeNameOf
  , edhTypeOf
  , edhValueNull
  , edhIdentEqual
  , edhNamelyEqual
  , edhValueEqual
  , edhValueRepr
  , edhValueReprTx
  , edhValueStr
  , edhValueStrTx
  , edhValueDesc
  , edhValueAsAttrKey
  , EdhValue(..)
  , EdhTypeValue(..)
  , edhDeCaseClose
  , edhDeCaseWrap
  , edhUltimate
  , nil
  , edhNone
  , edhNoneExpr
  , edhNothing
  , edhNothingExpr
  , edhNA
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
  , ProcDefi(..)
  , EdhGenrCaller
  , symbolName
  , globalSymbol
  , mkSymbol
  , mkUUID
  , mkDefault
  , EdhVector

    -- * argument exchanging
  , ArgsPack(..)
  , KwArgs
  , RestPosArgs
  , RestKwArgs
  , RestPackArgs
  , PositionalArgs(..)
  , KeywordArgs(..)
  , PackedArgs(..)
  , module Language.Edh.Args
  , module Language.Edh.InterOp

    -- * indexing and slicing support
  , EdhIndex(..)
  , parseEdhIndex
  , edhRegulateSlice
  , edhRegulateIndex

    -- * standalone modules
  , module Language.Edh.Details.IOPD
  )
where

import           Text.Megaparsec

import qualified Data.Lossless.Decimal         as D

import           Language.Edh.Args
import           Language.Edh.InterOp
import           Language.Edh.Control
import           Language.Edh.Batteries
import           Language.Edh.Runtime
import           Language.Edh.Event
import           Language.Edh.Details.IOPD
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.CoreLang
import           Language.Edh.Details.Evaluate
import           Language.Edh.Details.Utils

