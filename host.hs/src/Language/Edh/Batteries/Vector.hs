module Language.Edh.Batteries.Vector where

-- import           Debug.Trace

import Control.Concurrent.STM
  ( STM,
    TVar,
    newTVar,
    readTVar,
    writeTVar,
  )
import Data.Dynamic (toDyn)
import qualified Data.Lossless.Decimal as D
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector as V
import Data.Vector.Mutable (IOVector)
import qualified Data.Vector.Mutable as MV
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Control (EdhErrorTag (UsageError), OpSymbol)
import Language.Edh.Evaluate
import Language.Edh.IOPD (iopdUpdate, odLookup)
import Language.Edh.InterOp (wrapHostProc)
import Language.Edh.RtTypes
import Prelude

-- Boxed Vector for Edh values, non-transactional, mutable anytime
type EdhVector = IOVector EdhValue

createVectorClass :: Scope -> STM Object
createVectorClass !clsOuterScope =
  mkHostClass clsOuterScope "Vector" vecAllocator [] $ \ !clsScope -> do
    !mths <-
      sequence
        [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
          | (nm, vc, hp) <-
              [ ("append", EdhMethod, wrapHostProc vecAppendProc),
                ( "__eq__",
                  EdhMethod,
                  wrapHostProc vecEqProc
                ),
                -- TODO support vectorized (non)equality tests and ordering comparisons
                ( "[]",
                  EdhMethod,
                  wrapHostProc vecIdxReadProc
                ),
                -- TODO figure out the criteria and implementation of element-wise vector
                --      operations, trigger it just when 2 vectors have the same length?
                ("[=]", EdhMethod, wrapHostProc vecIdxWriteProc),
                ("[++=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc "++"),
                ("[+=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc "+"),
                ("[-=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc "-"),
                ("[*=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc "*"),
                ("[/=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc "/"),
                ("[//=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc "//"),
                ("[%=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc "%"),
                ("[**=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc "**"),
                ("[&&=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc "&&"),
                ("[||=]", EdhMethod, wrapHostProc $ vecIdxAssignWithOpProc "||"),
                ("(++)", EdhMethod, wrapHostProc $ vecCopyWithOpProc False "++"),
                ("(++.)", EdhMethod, wrapHostProc $ vecCopyWithOpProc True "++"),
                ("(+)", EdhMethod, wrapHostProc $ vecCopyWithOpProc False "+"),
                ("(+.)", EdhMethod, wrapHostProc $ vecCopyWithOpProc True "+"),
                ("(-)", EdhMethod, wrapHostProc $ vecCopyWithOpProc False "-"),
                ("(-.)", EdhMethod, wrapHostProc $ vecCopyWithOpProc True "-"),
                ("(*)", EdhMethod, wrapHostProc $ vecCopyWithOpProc False "*"),
                ("(*.)", EdhMethod, wrapHostProc $ vecCopyWithOpProc True "*"),
                ("(/)", EdhMethod, wrapHostProc $ vecCopyWithOpProc False "/"),
                ("(/.)", EdhMethod, wrapHostProc $ vecCopyWithOpProc True "/"),
                ("(//)", EdhMethod, wrapHostProc $ vecCopyWithOpProc False "//"),
                ("(//.)", EdhMethod, wrapHostProc $ vecCopyWithOpProc True "//"),
                ("(%)", EdhMethod, wrapHostProc $ vecCopyWithOpProc False "%"),
                ("(%.)", EdhMethod, wrapHostProc $ vecCopyWithOpProc True "%"),
                ("(**)", EdhMethod, wrapHostProc $ vecCopyWithOpProc False "**"),
                ("(**.)", EdhMethod, wrapHostProc $ vecCopyWithOpProc True "**"),
                ("(&&", EdhMethod, wrapHostProc $ vecCopyWithOpProc False "&&"),
                ("(&&@", EdhMethod, wrapHostProc $ vecCopyWithOpProc True "&&"),
                ("(||", EdhMethod, wrapHostProc $ vecCopyWithOpProc False "||"),
                ("(||@", EdhMethod, wrapHostProc $ vecCopyWithOpProc True "||"),
                ("(++=)", EdhMethod, wrapHostProc $ vecAssignWithOpProc "++"),
                ("(+=)", EdhMethod, wrapHostProc $ vecAssignWithOpProc "+"),
                ("(-=)", EdhMethod, wrapHostProc $ vecAssignWithOpProc "-"),
                ("(*=)", EdhMethod, wrapHostProc $ vecAssignWithOpProc "*"),
                ("(/=)", EdhMethod, wrapHostProc $ vecAssignWithOpProc "/"),
                ("(//=)", EdhMethod, wrapHostProc $ vecAssignWithOpProc "//"),
                ("(%=)", EdhMethod, wrapHostProc $ vecAssignWithOpProc "%"),
                ("(**=)", EdhMethod, wrapHostProc $ vecAssignWithOpProc "**"),
                ("(&&=)", EdhMethod, wrapHostProc $ vecAssignWithOpProc "&&"),
                ("(||=)", EdhMethod, wrapHostProc $ vecAssignWithOpProc "||"),
                ("__null__", EdhMethod, wrapHostProc vecNullProc),
                ("__len__", EdhMethod, wrapHostProc vecLenProc),
                ("__repr__", EdhMethod, wrapHostProc vecReprProc)
              ]
        ]
    iopdUpdate mths $ edh'scope'entity clsScope
  where
    vecAllocator :: ArgsPack -> EdhObjectAllocator
    vecAllocator (ArgsPack !ctorArgs !ctorKwargs) !ctorExit !etsCtor = do
      let doIt :: Int -> [EdhValue] -> STM ()
          -- note @vs@ got to be lazy
          doIt !len vs = do
            let !vec = case len of
                  _ | len < 0 -> V.fromList vs
                  _ -> V.fromListN len vs
            !mvec <- unsafeIOToSTM $ V.thaw vec
            !mvv <- newTVar mvec
            ctorExit $ HostStore $ toDyn mvv
      case odLookup (AttrByName "length") ctorKwargs of
        Nothing -> doIt (-1) ctorArgs
        Just (EdhDecimal !d) -> case D.decimalToInteger d of
          Just !len
            | len >= 0 ->
              doIt (fromInteger len) $ ctorArgs ++ repeat edhNA
          _ ->
            throwEdh etsCtor UsageError $
              "length not an positive integer: "
                <> T.pack (show d)
        Just !badLenVal ->
          throwEdh etsCtor UsageError $
            "invalid length: "
              <> T.pack
                (show badLenVal)

    vecAppendProc :: [EdhValue] -> EdhHostProc
    vecAppendProc !args !exit !ets =
      withThisHostObj ets $ \(mvv :: TVar EdhVector) ->
        readTVar mvv >>= \ !mvec -> do
          !mvec' <-
            unsafeIOToSTM $ V.thaw =<< (V.++ V.fromList args) <$> V.freeze mvec
          writeTVar mvv mvec'
          exitEdh ets exit $
            EdhObject $
              edh'scope'this $
                contextScope $
                  edh'context ets

    vecEqProc :: EdhValue -> EdhHostProc
    vecEqProc !other !exit !ets =
      castObjectStore' other >>= \case
        Nothing -> exitEdh ets exit $ EdhBool False
        Just (_, !mvecOther) -> withThisHostObj ets $ \(mvv :: TVar EdhVector) ->
          readTVar mvv >>= \ !mvec -> do
            !conclusion <- unsafeIOToSTM $ do
              -- TODO we're sacrificing thread safety for zero-copy performance
              --      here, justify this decision
              !vec <- V.unsafeFreeze mvec
              !vecOther <- V.unsafeFreeze mvecOther
              return $ vec == vecOther
            exitEdh ets exit $ EdhBool conclusion

    vecIdxReadProc :: EdhValue -> EdhHostProc
    vecIdxReadProc !idxVal !exit !ets =
      withThisHostObj ets $ \(mvv :: TVar EdhVector) ->
        readTVar mvv >>= \ !mvec -> do
          let exitWith :: EdhVector -> STM ()
              exitWith !newVec = do
                !newVV <- newTVar newVec
                let !newStore = HostStore (toDyn newVV)
                edhMutCloneObj ets thisVecObj (edh'scope'that scope) newStore $
                  \ !thatObjClone -> exitEdh ets exit $ EdhObject thatObjClone
              exitWithRange :: Int -> Int -> Int -> STM ()
              exitWithRange !start !stop !step = do
                !newVec <- unsafeIOToSTM $ do
                  let (q, r) = quotRem (stop - start) step
                      !len = if r == 0 then abs q else 1 + abs q
                  !newVec <- MV.new len
                  let cpElems :: Int -> Int -> IO ()
                      cpElems !n !i =
                        if i >= len
                          then return ()
                          else do
                            MV.unsafeRead mvec n >>= MV.unsafeWrite newVec i
                            cpElems (n + step) (i + 1)
                  cpElems start 0
                  return newVec
                exitWith newVec

          parseEdhIndex ets idxVal $ \case
            Left !err -> throwEdh ets UsageError err
            Right (EdhIndex !i) ->
              unsafeIOToSTM (MV.read mvec i) >>= exitEdh ets exit
            Right EdhAny -> exitEdh ets exit $ EdhObject thisVecObj
            Right EdhAll -> exitEdh ets exit $ EdhObject thisVecObj
            Right (EdhSlice !start !stop !step) ->
              edhRegulateSlice ets (MV.length mvec) (start, stop, step) $
                \(!iStart, !iStop, !iStep) ->
                  if iStep == 1
                    then exitWith $ MV.unsafeSlice iStart (iStop - iStart) mvec
                    else exitWithRange iStart iStop iStep
      where
        !scope = contextScope $ edh'context ets
        !thisVecObj = edh'scope'this scope

    vecIdxWriteProc :: EdhValue -> EdhValue -> EdhHostProc
    vecIdxWriteProc !idxVal !other !exit !ets =
      withThisHostObj ets $ \(mvv :: TVar EdhVector) ->
        readTVar mvv >>= \ !mvec -> do
          let exitWithRangeAssign :: Int -> Int -> Int -> STM ()
              exitWithRangeAssign !start !stop !step =
                castObjectStore' (edhUltimate other) >>= \case
                  Nothing -> exitWithNonVecAssign
                  Just (_, !mvecOther) -> do
                    unsafeIOToSTM $ assignWithVec start 0 mvecOther
                    exitEdh ets exit other
                where
                  (q, r) = quotRem (stop - start) step
                  !len = if r == 0 then abs q else 1 + abs q
                  exitWithNonVecAssign = case edhUltimate other of
                    EdhArgsPack (ArgsPack !args' _) -> do
                      unsafeIOToSTM $ assignWithList start $ take len args'
                      exitEdh ets exit other
                    EdhList (List _ !lsv) -> do
                      !ls <- readTVar lsv
                      unsafeIOToSTM $ assignWithList start $ take len ls
                      exitEdh ets exit other
                    !badList ->
                      throwEdh ets UsageError $
                        "not assignable to indexed vector: "
                          <> T.pack (edhTypeNameOf badList)
                  assignWithList :: Int -> [EdhValue] -> IO ()
                  assignWithList _ [] = return ()
                  assignWithList !n (x : xs) = do
                    MV.unsafeWrite mvec n x
                    assignWithList (n + step) xs
                  assignWithVec :: Int -> Int -> EdhVector -> IO ()
                  assignWithVec !n !i !mvec' =
                    if i >= len || i >= MV.length mvec'
                      then return ()
                      else do
                        MV.unsafeRead mvec' i >>= MV.unsafeWrite mvec n
                        assignWithVec (n + step) (i + 1) mvec'

          parseEdhIndex ets idxVal $ \case
            Left !err -> throwEdh ets UsageError err
            Right (EdhIndex !i) -> do
              unsafeIOToSTM $ MV.unsafeWrite mvec i other
              exitEdh ets exit other
            Right EdhAny -> do
              unsafeIOToSTM $ MV.set mvec other
              exitEdh ets exit other
            Right EdhAll -> exitWithRangeAssign 0 (MV.length mvec) 1
            Right (EdhSlice !start !stop !step) ->
              edhRegulateSlice ets (MV.length mvec) (start, stop, step) $
                \(!iStart, !iStop, !iStep) ->
                  exitWithRangeAssign iStart iStop iStep

    vecCopyWithOpProc :: Bool -> OpSymbol -> EdhValue -> EdhHostProc
    vecCopyWithOpProc !flipOperands !opSym !other !exit !ets =
      withThisHostObj ets $ \(mvv :: TVar EdhVector) ->
        readTVar mvv >>= \ !mvec ->
          unsafeIOToSTM (MV.new $ MV.length mvec) >>= \ !newVec ->
            let copyAt :: Int -> STM ()
                copyAt !n =
                  if n < 0
                    then do
                      !newVV <- newTVar newVec
                      let !newStore = HostStore (toDyn newVV)
                      edhMutCloneObj ets thisVecObj (edh'scope'that scope) newStore $
                        \ !thatObjClone -> exitEdh ets exit $ EdhObject thatObjClone
                    else
                      unsafeIOToSTM (MV.read mvec n) >>= \ !srcVal ->
                        runEdhTx ets $
                          ( if flipOperands
                              then
                                evalInfix
                                  opSym
                                  (LitExpr $ ValueLiteral other)
                                  (LitExpr $ ValueLiteral srcVal)
                              else
                                evalInfix
                                  opSym
                                  (LitExpr $ ValueLiteral srcVal)
                                  (LitExpr $ ValueLiteral other)
                          )
                            $ \ !rv _ets -> do
                              unsafeIOToSTM $ MV.unsafeWrite newVec n rv
                              copyAt (n - 1)
             in copyAt (MV.length mvec - 1)
      where
        !scope = contextScope $ edh'context ets
        !thisVecObj = edh'scope'this scope

    opAssignElems ::
      EdhThreadState ->
      OpSymbol ->
      EdhValue ->
      EdhVector ->
      Int ->
      Int ->
      Int ->
      STM () ->
      STM ()
    opAssignElems !ets !opSym !rhVal !mvec !start !stop !step !exit =
      assignAt
        start
      where
        assignAt :: Int -> STM ()
        assignAt !n =
          if n >= stop
            then exit
            else
              unsafeIOToSTM (MV.read mvec n) >>= \ !oldVal ->
                runEdhTx ets $
                  evalInfix
                    opSym
                    (LitExpr $ ValueLiteral oldVal)
                    (LitExpr $ ValueLiteral rhVal)
                    $ \ !opRtnV _ets -> do
                      unsafeIOToSTM $ MV.unsafeWrite mvec n opRtnV
                      assignAt (n + step)

    vecAssignWithOpProc :: OpSymbol -> EdhValue -> EdhHostProc
    vecAssignWithOpProc !opSym !other !exit !ets =
      withThisHostObj ets $ \(mvv :: TVar EdhVector) ->
        readTVar mvv >>= \ !mvec ->
          opAssignElems ets opSym other mvec 0 (MV.length mvec) 1 $
            exitEdh ets exit $
              EdhObject thisVecObj
      where
        !scope = contextScope $ edh'context ets
        !thisVecObj = edh'scope'this scope

    opAssignRange ::
      EdhThreadState ->
      OpSymbol ->
      EdhValue ->
      EdhVector ->
      Int ->
      Int ->
      Int ->
      EdhTxExit ->
      STM ()
    opAssignRange !ets !opSym !rhVal !mvec !start !stop !step !exit =
      castObjectStore' (edhUltimate rhVal) >>= \case
        Nothing -> exitWithNonVecAssign
        Just (_, !mvecOther) -> assignWithVec start 0 mvecOther
      where
        (q, r) = quotRem (stop - start) step
        !len = if r == 0 then abs q else 1 + abs q
        exitWithNonVecAssign = case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !args' _) -> assignWithList start $ take len args'
          EdhList (List _ !lsv) -> do
            !ls <- readTVar lsv
            assignWithList start $ take len ls
          _ ->
            opAssignElems ets opSym rhVal mvec start stop step $
              exitEdh ets exit nil
        assignWithList :: Int -> [EdhValue] -> STM ()
        assignWithList _ [] = exitEdh ets exit nil
        assignWithList !n (x : xs) =
          unsafeIOToSTM (MV.read mvec n) >>= \ !oldVal ->
            runEdhTx ets $
              evalInfix
                opSym
                (LitExpr $ ValueLiteral oldVal)
                (LitExpr $ ValueLiteral x)
                $ \ !opRtnV _ets -> do
                  unsafeIOToSTM $ MV.unsafeWrite mvec n opRtnV
                  assignWithList (n + step) xs
        assignWithVec :: Int -> Int -> EdhVector -> STM ()
        assignWithVec !n !i !mvec' =
          if i >= len || i >= MV.length mvec'
            then exitEdh ets exit nil
            else do
              !oldVal <- unsafeIOToSTM $ MV.unsafeRead mvec n
              !otherVal <- unsafeIOToSTM $ MV.unsafeRead mvec' i
              runEdhTx ets $
                evalInfix
                  opSym
                  (LitExpr $ ValueLiteral oldVal)
                  (LitExpr $ ValueLiteral otherVal)
                  $ \ !opRtnV _ets -> do
                    unsafeIOToSTM $ MV.unsafeWrite mvec n opRtnV
                    assignWithVec (n + step) (i + 1) mvec'

    vecIdxAssignWithOpProc :: OpSymbol -> EdhValue -> EdhValue -> EdhHostProc
    vecIdxAssignWithOpProc !opSym !idxVal !other !exit !ets =
      withThisHostObj ets $ \(mvv :: TVar EdhVector) ->
        readTVar mvv >>= \ !mvec -> parseEdhIndex ets idxVal $ \case
          Left !err -> throwEdh ets UsageError err
          Right (EdhIndex !i) ->
            unsafeIOToSTM (MV.read mvec i) >>= \ !oldVal ->
              runEdhTx ets $
                evalInfix
                  opSym
                  (LitExpr $ ValueLiteral oldVal)
                  (LitExpr $ ValueLiteral other)
                  $ \ !opRtnV _ets -> do
                    unsafeIOToSTM $ MV.unsafeWrite mvec i opRtnV
                    exitEdh ets exit opRtnV
          Right EdhAny ->
            opAssignElems ets opSym other mvec 0 (MV.length mvec) 1 $
              exitEdh ets exit nil
          Right EdhAll ->
            opAssignRange ets opSym other mvec 0 (MV.length mvec) 1 exit
          Right (EdhSlice !start !stop !step) ->
            edhRegulateSlice ets (MV.length mvec) (start, stop, step) $
              \(!iStart, !iStop, !iStep) ->
                opAssignRange ets opSym other mvec iStart iStop iStep exit

    vecNullProc :: EdhHostProc
    vecNullProc !exit !ets = withThisHostObj ets $ \(mvv :: TVar EdhVector) ->
      readTVar mvv >>= \ !mvec -> exitEdh ets exit $ EdhBool $ MV.length mvec <= 0

    vecLenProc :: EdhHostProc
    vecLenProc !exit !ets = withThisHostObj ets $ \(mvv :: TVar EdhVector) ->
      readTVar mvv >>= \ !mvec ->
        exitEdh ets exit $ EdhDecimal $ fromIntegral $ MV.length mvec

    vecReprProc :: EdhHostProc
    vecReprProc !exit !ets = withThisHostObj ets $ \(mvv :: TVar EdhVector) ->
      readTVar mvv >>= \ !mvec -> do
        let go :: [EdhValue] -> [Text] -> STM ()
            go [] !rs =
              exitEdh ets exit $
                EdhString $
                  "Vector("
                    <> T.intercalate "," (reverse rs)
                    <> ")"
            go (v : rest) rs = edhValueRepr ets v $ \ !r -> go rest (r : rs)
        !vec <- unsafeIOToSTM $ V.freeze mvec
        go (V.toList vec) []
