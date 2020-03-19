
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
import           Language.Edh.Runtime


-- | operator ($) - dereferencing attribute addressor
attrDerefAddrProc :: EdhProcedure
attrDerefAddrProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit =
  evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case rhVal of
    EdhString !attrName -> getEdhAttr
      lhExpr
      (AttrByName attrName)
      (\lhVal ->
        throwEdh EvalError
          $  "No such attribute "
          <> attrName
          <> " from "
          <> T.pack (show lhVal)
      )
      exit
    EdhSymbol sym@(Symbol _ desc) -> getEdhAttr
      lhExpr
      (AttrBySym sym)
      (\lhVal ->
        throwEdh EvalError $ "No such attribute @" <> desc <> " from " <> T.pack
          (show lhVal)
      )
      exit
    _ -> throwEdh EvalError $ "Invalid attribute reference type - " <> T.pack
      (show $ edhTypeOf rhVal)
attrDerefAddrProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)


-- | operator (:=) - value definition
defProc :: EdhProcedure
defProc [SendPosArg (AttrExpr (DirectRef (NamedAttr !valName))), SendPosArg !rhExpr] !exit
  = do
    pgs <- ask
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> contEdhSTM $ do
      let !ent = scopeEntity $ contextScope $ edh'context pgs
          nv   = EdhNamedValue valName rhVal
      lookupEntityAttr pgs ent (AttrByName valName) >>= \case
        EdhNil -> do
          changeEntityAttr pgs ent (AttrByName valName) nv
          exitEdhSTM pgs exit nv
        oldDef@(EdhNamedValue n v) -> if v /= rhVal
          then
            runEdhProg pgs $ edhValueRepr rhVal $ \(OriginalValue newR _ _) ->
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
defProc !argsSender _ =
  throwEdh EvalError $ "Invalid value definition: " <> T.pack (show argsSender)


-- | operator (:) - pair constructor
consProc :: EdhProcedure
consProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit = do
  pgs <- ask
  -- make sure left hand and right hand values are evaluated in same tx
  local (const pgs { edh'in'tx = True })
    $ evalExpr lhExpr
    $ \(OriginalValue !lhVal _ _) ->
        evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
          contEdhSTM $ exitEdhSTM pgs exit (EdhPair lhVal rhVal)
consProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)


-- | operator (?) - attribute tempter, 
-- address an attribute off an object if possible, nil otherwise
attrTemptProc :: EdhProcedure
attrTemptProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit = do
  !pgs <- ask
  case rhExpr of
    AttrExpr (DirectRef !addr) -> contEdhSTM $ do
      key <- resolveAddr pgs addr
      runEdhProg pgs $ getEdhAttr lhExpr key (const $ exitEdhProc exit nil) exit
    _ -> throwEdh EvalError $ "Invalid attribute expression: " <> T.pack
      (show rhExpr)
attrTemptProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)

-- | operator (?$) - attribute dereferencing tempter, 
-- address an attribute off an object if possible, nil otherwise
attrDerefTemptProc :: EdhProcedure
attrDerefTemptProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit =
  evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case rhVal of
    EdhString !attrName -> getEdhAttr lhExpr
                                      (AttrByName attrName)
                                      (const $ exitEdhProc exit nil)
                                      exit
    EdhSymbol !sym ->
      getEdhAttr lhExpr (AttrBySym sym) (const $ exitEdhProc exit nil) exit
    _ -> throwEdh EvalError $ "Invalid attribute reference type - " <> T.pack
      (show $ edhTypeOf rhVal)
attrDerefTemptProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)


-- | the Symbol(description) constructor
symbolCtorProc :: EdhProcedure
symbolCtorProc !argsSender !exit = do
  !pgs <- ask
  packEdhArgs argsSender $ \(ArgsPack !args _) -> contEdhSTM $ case args of
    [EdhString description] -> do
      sym <- mkSymbol description
      exitEdhSTM pgs exit $ EdhSymbol sym
    _ -> throwEdhSTM pgs EvalError "Invalid arg to Symbol()"


-- | utility pkargs(*args,**kwargs,***packed) - arguments packer
pkargsProc :: EdhProcedure
pkargsProc !argsSender !exit =
  packEdhArgs argsSender $ \apk -> exitEdhProc exit (EdhArgsPack apk)


-- | operator (++) - string coercing concatenator
concatProc :: EdhProcedure
concatProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    edhValueStr lhVal $ \(OriginalValue lhStr _ _) -> case lhStr of
      EdhString !lhs -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
        edhValueStr rhVal $ \(OriginalValue rhStr _ _) -> case rhStr of
          EdhString !rhs -> exitEdhProc exit (EdhString $ lhs <> rhs)
          _              -> error "bug: edhValueStr returned non-string"
      _ -> error "bug: edhValueStr returned non-string"
 where
  edhValueStr :: EdhValue -> EdhProcExit -> EdhProg (STM ())
  edhValueStr s@EdhString{} !exit' = exitEdhProc exit' s
  edhValueStr !v            !exit' = edhValueRepr v exit'
concatProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)


-- | utility null(*args,**kwargs) - null tester
isNullProc :: EdhProcedure
isNullProc !argsSender !exit = do
  !pgs <- ask
  packEdhArgs argsSender $ \(ArgsPack !args !kwargs) -> if null kwargs
    then case args of
      [v] -> contEdhSTM $ do
        isNull <- EdhBool <$> edhValueNull v
        exitEdhSTM pgs exit isNull
      _ -> contEdhSTM $ do
        argsNulls <- sequence $ ((EdhBool <$>) . edhValueNull) <$> args
        exitEdhSTM pgs exit (EdhTuple argsNulls)
    else contEdhSTM $ do
      argsNulls   <- sequence $ ((EdhBool <$>) . edhValueNull) <$> args
      kwargsNulls <- sequence $ Map.map ((EdhBool <$>) . edhValueNull) kwargs
      exitEdhSTM pgs exit (EdhArgsPack $ ArgsPack argsNulls kwargsNulls)


-- | utility type(*args,**kwargs) - value type introspector
typeProc :: EdhProcedure
typeProc !argsSender !exit =
  packEdhArgs argsSender $ \(ArgsPack !args !kwargs) ->
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
  edhTypeValOf (EdhNamedValue _ v) = edhTypeValOf v
  edhTypeValOf v                   = EdhType $ edhTypeOf v

-- | utility dict(***pkargs,**kwargs,*args) - dict constructor by arguments
-- can be used to convert arguments pack into dict
dictProc :: EdhProcedure
dictProc !argsSender !exit = do
  !pgs <- ask
  packEdhArgs argsSender $ \(ArgsPack !args !kwargs) ->
    let !kwDict =
            Map.fromList $ (<$> Map.toList kwargs) $ \(attrName, val) ->
              (EdhString attrName, val)
    in  contEdhSTM $ do
          u <- unsafeIOToSTM newUnique
          d <- newTVar $ Map.union kwDict $ Map.fromList
            [ (EdhDecimal (fromIntegral i), t)
            | (i, t) <- zip [(0 :: Int) ..] args
            ]
          exitEdhSTM pgs exit (EdhDict (Dict u d))


val2DictEntry :: EdhProgState -> EdhValue -> STM (ItemKey, EdhValue)
val2DictEntry _ (EdhPair !k !v    ) = return (k, v)
val2DictEntry _ (EdhTuple [!k, !v]) = return (k, v)
val2DictEntry _ (EdhArgsPack (ArgsPack [!k, !v] !kwargs)) | Map.null kwargs =
  return (k, v)
val2DictEntry !pgs !val =
  throwEdhSTM pgs EvalError
    $  "Invalid entry for dict "
    <> T.pack (show $ edhTypeOf val)
    <> ": "
    <> T.pack (show val)


-- | operator (?<=) - element-of tester
elemProc :: EdhProcedure
elemProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case rhVal of
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
          <> T.pack (show $ edhTypeOf rhVal)
          <> ": "
          <> T.pack (show rhVal)
elemProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)

-- | operator (=>) - prepender
prpdProc :: EdhProcedure
prpdProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case rhVal of
      EdhTuple vs          -> exitEdhProc exit (EdhTuple $ lhVal : vs)
      EdhList  (List _ !l) -> contEdhSTM $ do
        modifyTVar' l (lhVal :)
        exitEdhSTM pgs exit rhVal
      EdhDict (Dict _ !d) -> contEdhSTM $ do
        (k, v) <- val2DictEntry pgs lhVal
        modifyTVar' d (setDictItem k v)
        exitEdhSTM pgs exit rhVal
      _ ->
        throwEdh EvalError
          $  "Don't know how to prepend to a "
          <> T.pack (show $ edhTypeOf rhVal)
          <> ": "
          <> T.pack (show rhVal)
prpdProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)

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
cprhProc :: EdhProcedure
cprhProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit = do
  !pgs <- ask
  let pvlToDict :: [EdhValue] -> STM DictStore
      pvlToDict ps = Map.fromList <$> sequence (val2DictEntry pgs <$> ps)
      insertToDict :: EdhValue -> TVar DictStore -> STM ()
      insertToDict p d = do
        (k, v) <- val2DictEntry pgs p
        modifyTVar' d $ setDictItem k v
  case rhExpr of
    ForExpr argsRcvr iterExpr doExpr ->
      evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case lhVal of
        EdhList (List _ !l) -> contEdhSTM $ edhForLoop
          pgs
          argsRcvr
          iterExpr
          doExpr
          (\val -> modifyTVar' l (++ [val]))
          (\mkLoop -> runEdhProg pgs $ mkLoop $ \_ -> exitEdhProc exit lhVal)
        EdhDict (Dict _ !d) -> contEdhSTM $ edhForLoop
          pgs
          argsRcvr
          iterExpr
          doExpr
          (\val -> insertToDict val d)
          (\mkLoop -> runEdhProg pgs $ mkLoop $ \_ -> exitEdhProc exit lhVal)
        EdhTuple vs -> contEdhSTM $ do
          l <- newTVar []
          edhForLoop pgs
                     argsRcvr
                     iterExpr
                     doExpr
                     (\val -> modifyTVar' l (val :))
            $ \mkLoop -> runEdhProg pgs $ mkLoop $ \_ -> contEdhSTM $ do
                vs' <- readTVar l
                exitEdhSTM pgs exit (EdhTuple $ vs ++ reverse vs')
        _ ->
          throwEdh EvalError
            $  "Don't know how to comprehend into a "
            <> T.pack (show $ edhTypeOf lhVal)
            <> ": "
            <> T.pack (show lhVal)
    _ -> evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
      evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case lhVal of
        EdhTuple vs -> case rhVal of
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
              <> T.pack (show $ edhTypeOf rhVal)
              <> ": "
              <> T.pack (show rhVal)
        EdhList (List _ !l) -> case rhVal of
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
              <> T.pack (show $ edhTypeOf rhVal)
              <> ": "
              <> T.pack (show rhVal)
        EdhDict (Dict _ !d) -> case rhVal of
          EdhArgsPack (ArgsPack !args !kwargs) | Map.null kwargs ->
            contEdhSTM $ do
              d' <- pvlToDict args
              modifyTVar d $ Map.union d'
              exitEdhSTM pgs exit lhVal
          EdhTuple vs -> contEdhSTM $ do
            d' <- pvlToDict vs
            modifyTVar d $ Map.union d'
            exitEdhSTM pgs exit lhVal
          EdhList (List _ !l) -> contEdhSTM $ do
            ll <- readTVar l
            d' <- pvlToDict ll
            modifyTVar d $ Map.union d'
            exitEdhSTM pgs exit lhVal
          EdhDict (Dict _ !d') -> contEdhSTM $ do
            ds <- readTVar d'
            modifyTVar d $ Map.union ds
            exitEdhSTM pgs exit lhVal
          _ ->
            throwEdh EvalError
              $  "Don't know how to comprehend from a "
              <> T.pack (show $ edhTypeOf rhVal)
              <> ": "
              <> T.pack (show rhVal)
        _ ->
          throwEdh EvalError
            $  "Don't know how to comprehend into a "
            <> T.pack (show $ edhTypeOf lhVal)
            <> ": "
            <> T.pack (show lhVal)
cprhProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)


-- | operator (<-) - event publisher
evtPubProc :: EdhProcedure
evtPubProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) -> case lhVal of
    EdhSink es -> evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      contEdhSTM $ do
        publishEvent es rhVal
        exitEdhSTM pgs exit rhVal
    _ ->
      throwEdh EvalError
        $  "Can only publish event to a sink, not a "
        <> T.pack (show $ edhTypeOf lhVal)
        <> ": "
        <> T.pack (show lhVal)
evtPubProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)

