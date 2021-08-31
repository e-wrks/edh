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
  ( -- * Exceptions
    EdhError (..),
    EdhErrorTag (..),
    ParserError,
    EdhCallFrame (..),
    PeerSite,
    ErrDetails,
    ErrMessage,
    ErrContext,
    edhKnownError,
    errorBundlePretty,

    -- * Context information
    SrcDoc (..),
    SrcPos (..),
    SrcRange (..),
    SrcLoc (..),
    srcPosCmp2Range,
    prettySrcLoc,
    beginningSrcPos,
    zeroSrcRange,
    noSrcRange,
    prettySrcPos,
    prettySrcRange,
    lspSrcPosFromParsec,
    lspSrcLocFromParsec,
    edhScopeSrcLoc,
    contextScope,
    contextSrcLoc,
    callingScope,
    callingSrcLoc,
    callingFrame,

    -- * Event processing
    EdhSink (..),
    newEdhSink,
    newEdhSink',
    subscribeEvents,
    postEvent,
    postEdhEvent,
    forkEventProducer,
    forkEventConsumer,
    waitEventConsumer,

    -- * STM/IO API for spliced interpreter

    -- ** Console interface w/ a default implementation
    EdhConsole (..),
    EdhConsoleIO (..),
    EdhLogger,
    LogLevel,
    defaultEdhConsole,
    defaultEdhConsoleSettings,

    -- ** World bootstraping
    EdhWorld (..),
    createEdhWorld,
    worldContext,
    installEdhBatteries,
    declareEdhOperators,

    -- ** Spliced execution
    performEdhEffect,
    performEdhEffect',
    behaveEdhEffect,
    behaveEdhEffect',
    fallbackEdhEffect,
    fallbackEdhEffect',
    runEdhModule,
    runEdhModule',
    runEdhFile,
    runEdhFile',
    EdhModulePreparation,
    edhModuleAsIs,
    createEdhModule,
    installEdhModule,
    importEdhModule,
    moduleContext,
    parseEdh,
    parseEdh',
    evalEdh,
    evalEdh',
    haltEdhProgram,
    runEdhProgram,
    runEdhProgram',
    callMagicMethod,
    invokeMagic,
    edhMakeCall,
    edhMakeCall',
    edhPrepareCall,
    edhPrepareCall',
    callEdhMethod,
    evalStmt,
    evalStmtSrc,
    evalExpr,
    evalExprSrc,
    evalExprs,
    evalInfix,
    evalInfixSrc,
    evalInfix',
    evalInfixSrc',
    pushEdhStack,
    pushEdhStack',
    recvEdhArgs,
    packEdhExprs,
    packEdhArgs,
    defineEffect,
    prepareEffStore,
    prepareEffStore',
    prepareExpStore,
    prepareExpStore',
    EdhProgState (..),
    EdhThreadState (..),
    EdhTask (..),
    Context (..),
    Scope (..),
    EdhProcDefi (..),
    callableName,
    callableDoc,
    EdhTx,
    EdhTxExit,
    EdhProc,
    EdhHostProc,
    EdhIntrinsicOp,
    edhFlipOp,

    -- ** Monadic Interface
    Edh (..),
    runEdh,
    edhInlineSTM,
    edhLiftSTM,
    liftEdhTx,
    performM,
    performM',
    behaveM,
    behaveM',
    fallbackM,
    fallbackM',
    edhThreadState,
    edhProgramState,
    readTVarEdh,
    writeTVarEdh,
    readIORefEdh,
    writeIORefEdh,
    edhCall,
    edhCall',
    edhObjStrM,
    edhValueStrM,
    edhObjReprM,
    edhValueReprM,
    edhObjDescM,
    edhValueDescM,
    edhSimpleDescM,
    edhValueNullM,
    edhValueJsonM,
    edhValueBlobM,
    edhValueBlobM',
    parseEdhIndexM,
    regulateEdhIndexM,
    regulateEdhSliceM,
    throwEdhM,
    throwEdhM',

    -- ** Edh Runtime error
    getEdhErrCtx,
    edhCreateError,
    edhThrow,
    edhCatch,
    edhThrowTx,
    edhCatchTx,
    throwEdh,
    throwEdh',
    throwEdhTx,
    throwHostSTM,
    throwHostSTM',
    throwHostIO,
    throwHostIO',

    -- ** Returning / Yielding
    runEdhTx,
    exitEdh,
    exitEdhTx,
    edhYield,

    -- ** CPS helpers
    seqcontSTM,
    seqEdhTx,

    -- ** Sync utilities
    edhDoSTM,
    endOfEdh,
    forkEdh,
    edhContSTM,
    edhContSTM',
    edhContSTM'',
    edhContSTM''',
    edhContIO,
    edhContIO',
    edhContIO'',
    edhContIO''',

    -- ** Reflective manipulation
    OptDocCmt (..),
    StmtSrc (..),
    stmtSrcSpan,
    Stmt (..),
    ExprSrc (..),
    exprSrcSpan,
    Expr (..),
    SourceSeg (..),
    deExpr,
    deExpr',
    deExpr1,
    deExpr'1,
    deParen,
    deParen',
    deParen1,
    deParen'1,
    deApk,
    deApk1,
    Prefix (..),
    Literal (..),
    AttrName,
    OpSymbol,
    OpFixity (..),
    OpSymSrc (..),
    Precedence,
    OpDeclLoc,
    DictKeyExpr (..),
    AttrRef (..),
    attrRefSpan,
    AttrAddrSrc (..),
    AttrAddr (..),
    attrAddrStr,
    ArgsReceiver (..),
    ArgReceiver (..),
    ArgsPacker (..),
    ArgSender (..),
    sentArgExprSrc,
    argSenderSpan,
    ProcDecl (..),
    procedureName,

    -- ** Object system
    Object (..),
    ObjectStore (..),
    castObjectStore,
    castObjectStore',
    castObjSelfStore,
    castObjSelfStore',
    withThisHostObj,
    withThisHostObj',
    withHostObject,
    withHostObject',
    withDerivedHostObject,
    withDerivedHostObject',
    EdhObjectAllocator,
    Class (..),
    objClass,
    edhClassName,
    objClassName,
    edhCreateHostObj,
    edhCreateHostObj',
    edhConstructObj,
    edhMutCloneObj,
    edhCloneHostObj,
    EntityStore,
    AttrKey (..),
    attrKeyStr,
    attrKeyValue,
    getObjAttrWithMagic,
    getObjAttrWithMagic',
    setObjAttrWithMagic,
    lookupEdhCtxAttr,
    resolveEdhCtxAttr,
    lookupEdhObjAttr,
    lookupEdhObjMagic,
    lookupEdhSuperAttr,
    resolveEdhInstance,
    objectScope,
    mkScopeWrapper,
    edhWrapHostValue,
    edhWrapHostValue',
    edhWrapHostValue'',
    mkHostClass,
    mkHostClass',
    mkObjSandbox,
    mkScopeSandbox,
    newSandbox,
    runEdhInSandbox,
    runEdhTxInSandbox,

    -- ** Value system
    edhSetValue,
    createEdhDict,
    setDictItem,
    lookupDictItem,
    dictEntryList,
    edhTypeNameOf,
    edhValueNull,
    edhValueNullTx,
    edhCompareValue,
    edhIdentEqual,
    edhNamelyEqual,
    edhValueEqual,
    edhValueIdent,
    edhObjRepr,
    edhObjReprTx,
    edhValueRepr,
    edhValueReprTx,
    edhObjStr,
    edhObjStrTx,
    edhValueStr,
    edhValueStrTx,
    edhValueBlob,
    edhValueBlobTx,
    edhValueBlob',
    edhValueBlobTx',
    edhValueDesc,
    edhValueDescTx,
    edhObjDesc,
    edhObjDescTx,
    edhObjDesc',
    edhObjDescTx',
    edhSimpleDesc,
    edhSimpleDescTx,
    edhValueJson,
    edhValueJsonTx,
    edhValueAsAttrKey,
    EdhValue (..),
    EdhBound (..),
    edhBoundValue,
    edhDeCaseClose,
    edhDeCaseWrap,
    edhDeFlowCtrl,
    edhUltimate,
    nil,
    edhNone,
    edhNothing,
    edhNA,
    edhNonNil,
    true,
    false,
    nan,
    inf,
    D.Decimal (..),
    Symbol (..),
    Dict (..),
    List (..),
    ProcDefi (..),
    EdhGenrCaller,
    symbolName,
    globalSymbol,
    mkSymbol,
    mkUUID,
    mkDefault,
    mkHostProc,
    mkSymbolicHostProc,
    EdhVector,

    -- * argument exchanging
    ArgsPack (..),
    KwArgs,
    RestPosArgs,
    RestKwArgs,
    RestPackArgs,
    PositionalArgs (..),
    KeywordArgs (..),
    PackedArgs (..),
    module Language.Edh.Args,
    module Language.Edh.InterOp,
    methodArrowArgsReceiver,
    producerArrowArgsReceiver,

    -- * indexing and slicing support
    EdhIndex (..),
    parseEdhIndex,
    regulateEdhSlice,

    -- * language harness
    normalizeModuRefSpec,
    locateEdhFile,
    locateEdhMainModule,

    -- * standalone modules
    module Language.Edh.IOPD,
    module Language.Edh.HostEvs,
    module Language.Edh.Batteries.Args,
    module Language.Edh.Batteries.Comput,
  )
where

import qualified Data.Lossless.Decimal as D
import Language.Edh.Args
import Language.Edh.Batteries
import Language.Edh.Batteries.Args
import Language.Edh.Batteries.Comput
import Language.Edh.Control
import Language.Edh.CoreLang
import Language.Edh.EdhEvs
import Language.Edh.Evaluate
import Language.Edh.HostEvs
import Language.Edh.IOPD
import Language.Edh.InterOp
import Language.Edh.PkgMan
import Language.Edh.RtTypes
import Language.Edh.Runtime
import Language.Edh.Utils
import Text.Megaparsec
