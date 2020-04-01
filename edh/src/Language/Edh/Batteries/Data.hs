
module Language.Edh.Batteries.Data where

import           Prelude
-- import           Debug.Trace

import           GHC.Conc                       ( unsafeIOToSTM )

import           Control.Monad.Reader
import           Control.Concurrent.STM

import           Data.Unique
import qualified Data.Text                     as T
import qualified Data.HashMap.Strict           as Map

import           Language.Edh.Control
import           Language.Edh.Event
import           Language.Edh.Details.RtTypes
import           Language.Edh.Details.Evaluate
import           Language.Edh.Details.Utils


-- | operator ($) - dereferencing attribute addressor
attrDerefAddrProc :: EdhIntrinsicOp
attrDerefAddrProc !lhExpr !rhExpr !exit =
  evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case edhUltimate rhVal of
    EdhExpr _ (AttrExpr (DirectRef !addr)) _ -> ask >>= \pgs ->
      contEdhSTM
        $ resolveEdhAttrAddr pgs addr
        $ \key -> runEdhProc pgs
            $ getEdhAttr lhExpr key (noAttr $ T.pack $ show key) exit
    EdhString !attrName ->
      getEdhAttr lhExpr (AttrByName attrName) (noAttr attrName) exit
    EdhSymbol sym@(Symbol _ desc) ->
      getEdhAttr lhExpr (AttrBySym sym) (noAttr $ "@" <> desc) exit
    _ -> throwEdh EvalError $ "Invalid attribute reference type - " <> T.pack
      (show $ edhTypeOf rhVal)
 where
  noAttr key lhVal =
    throwEdh EvalError
      $  "No such attribute "
      <> key
      <> " from a "
      <> T.pack (edhTypeNameOf lhVal)
      <> ": "
      <> T.pack (show lhVal)

-- | operator (:=) - value definition
defProc :: EdhIntrinsicOp
defProc (AttrExpr (DirectRef (NamedAttr !valName))) !rhExpr !exit = do
  pgs <- ask
  evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> contEdhSTM $ do
    let !ent = scopeEntity $ contextScope $ edh'context pgs
        nv   = EdhNamedValue valName rhVal
    lookupEntityAttr pgs ent (AttrByName valName) >>= \case
      EdhNil -> do
        changeEntityAttr pgs ent (AttrByName valName) nv
        exitEdhSTM pgs exit nv
      oldDef@(EdhNamedValue n v) -> if v /= rhVal
        then runEdhProc pgs $ edhValueRepr rhVal $ \(OriginalValue newR _ _) ->
          edhValueRepr oldDef $ \(OriginalValue oldR _ _) -> case newR of
            EdhString !newRepr -> case oldR of
              EdhString oldRepr ->
                throwEdh EvalError
                  $  "Can not redefine "
                  <> valName
                  <> " from { "
                  <> oldRepr
                  <> " } to { "
                  <> newRepr
                  <> " }"
              _ -> error "bug: edhValueRepr returned non-string"
            _ -> error "bug: edhValueRepr returned non-string"
        else do
          unless (n == valName) -- avoid writing the entity if all same
            $ changeEntityAttr pgs ent (AttrByName valName) nv
          exitEdhSTM pgs exit nv
      _ -> do
        changeEntityAttr pgs ent (AttrByName valName) nv
        exitEdhSTM pgs exit nv
defProc !lhExpr _ _ =
  throwEdh EvalError $ "Invalid value definition: " <> T.pack (show lhExpr)


-- | operator (:) - pair constructor
consProc :: EdhIntrinsicOp
consProc !lhExpr !rhExpr !exit = do
  pgs <- ask
  -- make sure left hand and right hand values are evaluated in same tx
  local (const pgs { edh'in'tx = True })
    $ evalExpr lhExpr
    $ \(OriginalValue !lhVal _ _) ->
        evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
          contEdhSTM $ exitEdhSTM pgs exit (EdhPair lhVal rhVal)


-- | operator (?) - attribute tempter, 
-- address an attribute off an object if possible, nil otherwise
attrTemptProc :: EdhIntrinsicOp
attrTemptProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  case rhExpr of
    AttrExpr (DirectRef !addr) ->
      contEdhSTM $ resolveEdhAttrAddr pgs addr $ \key ->
        runEdhProc pgs
          $ getEdhAttr lhExpr key (const $ exitEdhProc exit nil) exit
    _ -> throwEdh EvalError $ "Invalid attribute expression: " <> T.pack
      (show rhExpr)

-- | operator (?$) - attribute dereferencing tempter, 
-- address an attribute off an object if possible, nil otherwise
attrDerefTemptProc :: EdhIntrinsicOp
attrDerefTemptProc !lhExpr !rhExpr !exit =
  evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case edhUltimate rhVal of
    EdhExpr _ (AttrExpr (DirectRef !addr)) _ -> ask >>= \pgs ->
      contEdhSTM $ resolveEdhAttrAddr pgs addr $ \key ->
        runEdhProc pgs
          $ getEdhAttr lhExpr key (const $ exitEdhProc exit nil) exit
    EdhString !attrName -> getEdhAttr lhExpr
                                      (AttrByName attrName)
                                      (const $ exitEdhProc exit nil)
                                      exit
    EdhSymbol !sym ->
      getEdhAttr lhExpr (AttrBySym sym) (const $ exitEdhProc exit nil) exit
    _ -> throwEdh EvalError $ "Invalid attribute reference type - " <> T.pack
      (show $ edhTypeOf rhVal)


-- | the Symbol(description) constructor
symbolCtorProc :: EdhProcedure
symbolCtorProc (ArgsPack !args _) !exit = do
  !pgs <- ask
  contEdhSTM $ case args of
    [EdhString description] -> do
      sym <- mkSymbol description
      exitEdhSTM pgs exit $ EdhSymbol sym
    _ -> throwEdhSTM pgs EvalError "Invalid arg to Symbol()"


-- | utility pkargs(***apk) - arguments packer
pkargsProc :: EdhProcedure
pkargsProc !apk !exit = exitEdhProc exit (EdhArgsPack apk)


-- | utility repr(*args,**kwargs) - repr extractor
reprProc :: EdhProcedure
reprProc (ArgsPack !args !kwargs) !exit = do
  pgs <- ask
  let go
        :: [EdhValue]
        -> [(AttrName, EdhValue)]
        -> [EdhValue]
        -> [(AttrName, EdhValue)]
        -> STM ()
      go [repr] kwReprs [] [] | null kwReprs = exitEdhSTM pgs exit repr
      go reprs kwReprs [] [] =
        exitEdhSTM pgs exit
          $ EdhArgsPack
          $ ArgsPack (reverse reprs)
          $ Map.fromList kwReprs
      go reprs kwReprs (v : rest) kwps =
        runEdhProc pgs $ edhValueRepr v $ \(OriginalValue r _ _) ->
          contEdhSTM $ go (r : reprs) kwReprs rest kwps
      go reprs kwReprs [] ((k, v) : rest) =
        runEdhProc pgs $ edhValueRepr v $ \(OriginalValue r _ _) ->
          contEdhSTM $ go reprs ((k, r) : kwReprs) [] rest
  contEdhSTM $ go [] [] args (Map.toList kwargs)


-- | operator (++) - string coercing concatenator
concatProc :: EdhIntrinsicOp
concatProc !lhExpr !rhExpr !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    edhValueStr lhVal $ \(OriginalValue lhStr _ _) -> case lhStr of
      EdhString !lhs -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
        edhValueStr rhVal $ \(OriginalValue rhStr _ _) -> case rhStr of
          EdhString !rhs -> exitEdhProc exit (EdhString $ lhs <> rhs)
          _              -> error "bug: edhValueStr returned non-string"
      _ -> error "bug: edhValueStr returned non-string"
 where
  edhValueStr :: EdhValue -> EdhProcExit -> EdhProc
  edhValueStr s@EdhString{} !exit' = exitEdhProc exit' s
  edhValueStr !v            !exit' = edhValueRepr v exit'


-- | utility null(*args,**kwargs) - null tester
isNullProc :: EdhProcedure
isNullProc (ArgsPack !args !kwargs) !exit = do
  !pgs <- ask
  contEdhSTM $ if null kwargs
    then case args of
      [v] ->
        edhValueNull pgs v $ \isNull -> exitEdhSTM pgs exit $ EdhBool isNull
      _ -> seqcontSTM (edhValueNull pgs <$> args)
        $ \argsNulls -> exitEdhSTM pgs exit (EdhTuple $ EdhBool <$> argsNulls)
    else seqcontSTM (edhValueNull pgs <$> args) $ \argsNulls ->
      seqcontSTM
          [ \exit' -> edhValueNull pgs v (\isNull -> exit' (k, isNull))
          | (k, v) <- Map.toList kwargs
          ]
        $ \kwargsNulls -> exitEdhSTM
            pgs
            exit
            (EdhArgsPack $ ArgsPack
              (EdhBool <$> argsNulls)
              (Map.map EdhBool $ Map.fromList kwargsNulls)
            )


-- | utility type(*args,**kwargs) - value type introspector
typeProc :: EdhProcedure
typeProc (ArgsPack !args !kwargs) !exit =
  let !argsType = edhTypeValOf <$> args
  in  if null kwargs
        then case argsType of
          [t] -> exitEdhProc exit t
          _   -> exitEdhProc exit (EdhTuple argsType)
        else exitEdhProc
          exit
          (EdhArgsPack $ ArgsPack argsType $ Map.map edhTypeValOf kwargs)
 where
  edhTypeValOf :: EdhValue -> EdhValue
  edhTypeValOf EdhNil              = EdhNil
  edhTypeValOf (EdhNamedValue n v) = EdhNamedValue n $ edhTypeValOf v
  edhTypeValOf v                   = EdhType $ edhTypeOf v


-- | utility dict(***pkargs,**kwargs,*args) - dict constructor by arguments
-- can be used to convert arguments pack into dict
dictProc :: EdhProcedure
dictProc (ArgsPack !args !kwargs) !exit = do
  !pgs <- ask
  contEdhSTM $ do
    let !kwDict = Map.fromList $ (<$> Map.toList kwargs) $ \(attrName, val) ->
          (EdhString attrName, val)
    u <- unsafeIOToSTM newUnique
    d <- newTVar $ Map.union kwDict $ Map.fromList
      [ (EdhDecimal (fromIntegral i), t) | (i, t) <- zip [(0 :: Int) ..] args ]
    exitEdhSTM pgs exit (EdhDict (Dict u d))


-- | operator (?<=) - element-of tester
elemProc :: EdhIntrinsicOp
elemProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case edhUltimate rhVal of
      EdhTuple vs          -> exitEdhProc exit (EdhBool $ lhVal `elem` vs)
      EdhList  (List _ !l) -> contEdhSTM $ do
        ll <- readTVar l
        exitEdhSTM pgs exit $ EdhBool $ lhVal `elem` ll
      EdhDict (Dict _ !d) -> contEdhSTM $ do
        ds <- readTVar d
        exitEdhSTM pgs exit $ EdhBool $ case Map.lookup lhVal ds of
          Nothing -> False
          Just _  -> True
      _ ->
        throwEdh EvalError
          $  "Don't know how to prepend to a "
          <> T.pack (edhTypeNameOf rhVal)
          <> ": "
          <> T.pack (show rhVal)


-- | operator (=>) - prepender
prpdProc :: EdhIntrinsicOp
prpdProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case edhUltimate rhVal of
      EdhTuple vs          -> exitEdhProc exit (EdhTuple $ lhVal : vs)
      EdhList  (List _ !l) -> contEdhSTM $ do
        modifyTVar' l (lhVal :)
        exitEdhSTM pgs exit rhVal
      EdhDict (Dict _ !d) -> contEdhSTM $ val2DictEntry pgs lhVal $ \(k, v) ->
        do
          modifyTVar' d (setDictItem k v)
          exitEdhSTM pgs exit rhVal
      _ ->
        throwEdh EvalError
          $  "Don't know how to prepend to a "
          <> T.pack (edhTypeNameOf rhVal)
          <> ": "
          <> T.pack (show rhVal)


-- | operator (=<) - comprehension maker, appender
--  * list comprehension:
--     [] =< for x from range(10) do x*x
--  * dict comprehension:
--     {} =< for x from range(10) do (x, x*x)
--  * tuple comprehension:
--     (,) =< for x from range(10) do x*x
--  * list append
--      [] =< (...) / [...] / {...}
--  * dict append
--      {} =< (...) / [...] / {...}
--  * tuple append
--      (,) =< (...) / [...] / {...}
cprhProc :: EdhIntrinsicOp
cprhProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  let insertToDict :: EdhValue -> TVar DictStore -> STM ()
      insertToDict p d =
        val2DictEntry pgs p $ \(k, v) -> modifyTVar' d $ setDictItem k v
  case rhExpr of
    ForExpr argsRcvr iterExpr doExpr ->
      evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
        EdhList (List _ !l) -> contEdhSTM $ edhForLoop
          pgs
          argsRcvr
          iterExpr
          doExpr
          (\val -> modifyTVar' l (++ [val]))
          (\mkLoop -> runEdhProc pgs $ mkLoop $ \_ -> exitEdhProc exit lhVal)
        EdhDict (Dict _ !d) -> contEdhSTM $ edhForLoop
          pgs
          argsRcvr
          iterExpr
          doExpr
          (\val -> insertToDict val d)
          (\mkLoop -> runEdhProc pgs $ mkLoop $ \_ -> exitEdhProc exit lhVal)
        EdhTuple vs -> contEdhSTM $ do
          l <- newTVar []
          edhForLoop pgs
                     argsRcvr
                     iterExpr
                     doExpr
                     (\val -> modifyTVar' l (val :))
            $ \mkLoop -> runEdhProc pgs $ mkLoop $ \_ -> contEdhSTM $ do
                vs' <- readTVar l
                exitEdhSTM pgs exit (EdhTuple $ vs ++ reverse vs')
        _ ->
          throwEdh EvalError
            $  "Don't know how to comprehend into a "
            <> T.pack (edhTypeNameOf lhVal)
            <> ": "
            <> T.pack (show lhVal)
    _ -> evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
      evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case edhUltimate lhVal of
        EdhTuple vs -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !args !kwargs) | Map.null kwargs ->
            exitEdhProc exit (EdhTuple $ vs ++ args)
          EdhTuple vs'         -> exitEdhProc exit (EdhTuple $ vs ++ vs')
          EdhList  (List _ !l) -> contEdhSTM $ do
            ll <- readTVar l
            exitEdhSTM pgs exit (EdhTuple $ vs ++ ll)
          EdhDict (Dict _ !d) -> contEdhSTM $ do
            ds <- readTVar d
            exitEdhSTM pgs exit (EdhTuple $ vs ++ dictEntryList ds)
          _ ->
            throwEdh EvalError
              $  "Don't know how to comprehend from a "
              <> T.pack (edhTypeNameOf rhVal)
              <> ": "
              <> T.pack (show rhVal)
        EdhList (List _ !l) -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !args !kwargs) | Map.null kwargs ->
            contEdhSTM $ do
              modifyTVar' l (++ args)
              exitEdhSTM pgs exit lhVal
          EdhTuple vs -> contEdhSTM $ do
            modifyTVar' l (++ vs)
            exitEdhSTM pgs exit lhVal
          EdhList (List _ !l') -> contEdhSTM $ do
            ll <- readTVar l'
            modifyTVar' l (++ ll)
            exitEdhSTM pgs exit lhVal
          EdhDict (Dict _ !d) -> contEdhSTM $ do
            ds <- readTVar d
            modifyTVar' l (++ (dictEntryList ds))
            exitEdhSTM pgs exit lhVal
          _ ->
            throwEdh EvalError
              $  "Don't know how to comprehend from a "
              <> T.pack (edhTypeNameOf rhVal)
              <> ": "
              <> T.pack (show rhVal)
        EdhDict (Dict _ !d) -> case edhUltimate rhVal of
          EdhArgsPack (ArgsPack !args !kwargs) | Map.null kwargs ->
            contEdhSTM $ pvlToDict pgs args $ \d' -> do
              modifyTVar d $ Map.union d'
              exitEdhSTM pgs exit lhVal
          EdhTuple vs -> contEdhSTM $ pvlToDict pgs vs $ \d' -> do
            modifyTVar d $ Map.union d'
            exitEdhSTM pgs exit lhVal
          EdhList (List _ !l) -> contEdhSTM $ do
            ll <- readTVar l
            pvlToDict pgs ll $ \d' -> do
              modifyTVar d $ Map.union d'
              exitEdhSTM pgs exit lhVal
          EdhDict (Dict _ !d') -> contEdhSTM $ do
            ds <- readTVar d'
            modifyTVar d $ Map.union ds
            exitEdhSTM pgs exit lhVal
          _ ->
            throwEdh EvalError
              $  "Don't know how to comprehend from a "
              <> T.pack (edhTypeNameOf rhVal)
              <> ": "
              <> T.pack (show rhVal)
        _ ->
          throwEdh EvalError
            $  "Don't know how to comprehend into a "
            <> T.pack (edhTypeNameOf lhVal)
            <> ": "
            <> T.pack (show lhVal)


-- | operator (<-) - event publisher
evtPubProc :: EdhIntrinsicOp
evtPubProc !lhExpr !rhExpr !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case edhUltimate lhVal of
    EdhSink es -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ do
        publishEvent es rhVal
        exitEdhSTM pgs exit rhVal
    _ ->
      throwEdh EvalError
        $  "Can only publish event to a sink, not a "
        <> T.pack (edhTypeNameOf lhVal)
        <> ": "
        <> T.pack (show lhVal)

