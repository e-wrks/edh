
module Language.Edh.Batteries.Data where

import           Prelude
-- import           Debug.Trace

import           Control.Monad.Reader
import           Control.Concurrent.STM

import qualified Data.Text                     as T
import qualified Data.Map.Strict               as Map

import           Text.Megaparsec

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
      (  throwEdh EvalError
      $  "No such attribute "
      <> edhValueStr rhVal
      <> " from "
      <> T.pack (show lhExpr)
      )
      exit
    EdhSymbol !sym -> getEdhAttr
      lhExpr
      (AttrBySym sym)
      (  throwEdh EvalError
      $  "No such attribute "
      <> edhValueStr rhVal
      <> " from "
      <> T.pack (show lhExpr)
      )
      exit
    _ ->
      throwEdh EvalError
        $  "Invalid attribute reference - "
        <> edhValueStr (edhTypeOf rhVal)
        <> ": "
        <> edhValueStr rhVal
attrDerefAddrProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)


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
      runEdhProg pgs $ getEdhAttr lhExpr key (exitEdhProc exit nil) exit
    _ -> throwEdh EvalError $ "Invalid attribute expression: " <> T.pack
      (show rhExpr)
attrTemptProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)

-- | operator (?$) - attribute dereferencing tempter, 
-- address an attribute off an object if possible, nil otherwise
attrDerefTemptProc :: EdhProcedure
attrDerefTemptProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit =
  evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case rhVal of
    EdhString !attrName ->
      getEdhAttr lhExpr (AttrByName attrName) (exitEdhProc exit nil) exit
    EdhSymbol !sym ->
      getEdhAttr lhExpr (AttrBySym sym) (exitEdhProc exit nil) exit
    _ ->
      throwEdh EvalError
        $  "Invalid attribute reference - "
        <> edhValueStr (edhTypeOf rhVal)
        <> ": "
        <> edhValueStr rhVal
attrDerefTemptProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)


-- | the Symbol() constructor
symbolCtorProc :: EdhProcedure
symbolCtorProc !argsSender !exit = do
  !pgs <- ask
  let (StmtSrc (srcPos, _)) = contextStmt $ edh'context pgs
  packHostProcArgs argsSender $ \(ArgsPack !args !kwargs) -> contEdhSTM $ do
    posSyms <- sequence $ ctorSym <$> args
    kwSyms  <- sequence $ Map.map ctorSym kwargs
    if null kwargs
      then case posSyms of
        [] -> do
          sym <- ctorSym $ EdhString $ T.pack (sourcePosPretty srcPos)
          exitEdhSTM pgs exit sym
        [sym] -> exitEdhSTM pgs exit sym
        _     -> exitEdhSTM pgs exit (EdhTuple posSyms)
      else exitEdhSTM pgs exit (EdhArgsPack $ ArgsPack posSyms kwSyms)
 where
  ctorSym :: EdhValue -> STM EdhValue
  ctorSym = \case
    sym@(EdhSymbol _) -> return sym
    val               -> EdhSymbol <$> (mkSymbol $ T.unpack $ edhValueStr val)


-- | utility pkargs(*args,**kwargs,***packed) - arguments packer
pkargsProc :: EdhProcedure
pkargsProc !argsSender !exit =
  packHostProcArgs argsSender $ \apk -> exitEdhProc exit (EdhArgsPack apk)


-- | operator (++) - string coercing concatenator
concatProc :: EdhProcedure
concatProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit =
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
      exitEdhProc exit (EdhString $ edhValueStr lhVal <> edhValueStr rhVal)
concatProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)


-- | utility null(*args,**kwargs) - null tester
isNullProc :: EdhProcedure
isNullProc !argsSender !exit = do
  !pgs <- ask
  packHostProcArgs argsSender $ \(ArgsPack !args !kwargs) -> if null kwargs
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
  packHostProcArgs argsSender $ \(ArgsPack !args !kwargs) ->
    let !argsType = edhTypeOf <$> args
    in  if null kwargs
          then case argsType of
            [t] -> exitEdhProc exit t
            _   -> exitEdhProc exit (EdhTuple argsType)
          else exitEdhProc
            exit
            (EdhArgsPack $ ArgsPack argsType $ Map.map edhTypeOf kwargs)


-- | utility dict(***pkargs,**kwargs,*args) - dict constructor by arguments
-- can be used to convert arguments pack into dict
dictProc :: EdhProcedure
dictProc !argsSender !exit = do
  !pgs <- ask
  packHostProcArgs argsSender $ \(ArgsPack !args !kwargs) ->
    let !kwDict =
            Map.fromAscList $ (<$> Map.toAscList kwargs) $ \(attrName, val) ->
              (ItemByStr attrName, val)
    in  contEdhSTM $ do
          d <- newTVar $ Map.union kwDict $ Map.fromAscList
            [ (ItemByNum (fromIntegral i), t)
            | (i, t) <- zip [(0 :: Int) ..] args
            ]
          exitEdhSTM pgs exit (EdhDict (Dict d))


val2DictEntry :: EdhProgState -> EdhValue -> STM (ItemKey, EdhValue)
val2DictEntry _ (EdhPair (EdhString  s) v) = return (ItemByStr s, v)
val2DictEntry _ (EdhPair (EdhSymbol  s) v) = return (ItemBySym s, v)
val2DictEntry _ (EdhPair (EdhDecimal n) v) = return (ItemByNum n, v)
val2DictEntry _ (EdhPair (EdhBool    b) v) = return (ItemByBool b, v)
val2DictEntry _ (EdhPair (EdhType    t) v) = return (ItemByType t, v)
val2DictEntry _ (EdhPair (EdhClass   c) v) = return (ItemByClass c, v)
val2DictEntry pgs (EdhPair k _v) =
  throwEdhSTM pgs EvalError $ "Invalid key for dict: " <> T.pack (show k)
val2DictEntry _ (EdhArgsPack (ArgsPack [EdhString s, v] !kwargs))
  | Map.null kwargs = return (ItemByStr s, v)
val2DictEntry _ (EdhArgsPack (ArgsPack [EdhSymbol s, v] !kwargs))
  | Map.null kwargs = return (ItemBySym s, v)
val2DictEntry _ (EdhArgsPack (ArgsPack [EdhDecimal n, v] !kwargs))
  | Map.null kwargs = return (ItemByNum n, v)
val2DictEntry _ (EdhArgsPack (ArgsPack [EdhBool b, v] !kwargs))
  | Map.null kwargs = return (ItemByBool b, v)
val2DictEntry pgs (EdhArgsPack (ArgsPack [k, _v] !kwargs)) | Map.null kwargs =
  throwEdhSTM pgs EvalError $ "Invalid key for dict: " <> T.pack (show k)
val2DictEntry _ (EdhArgsPack (ArgsPack [EdhType t, v] !kwargs))
  | Map.null kwargs = return (ItemByType t, v)
val2DictEntry _ (EdhArgsPack (ArgsPack [EdhClass c, v] !kwargs))
  | Map.null kwargs = return (ItemByClass c, v)
val2DictEntry _ (EdhTuple [EdhString  s, v]) = return (ItemByStr s, v)
val2DictEntry _ (EdhTuple [EdhSymbol  s, v]) = return (ItemBySym s, v)
val2DictEntry _ (EdhTuple [EdhDecimal n, v]) = return (ItemByNum n, v)
val2DictEntry _ (EdhTuple [EdhBool    b, v]) = return (ItemByBool b, v)
val2DictEntry _ (EdhTuple [EdhType    t, v]) = return (ItemByType t, v)
val2DictEntry _ (EdhTuple [EdhClass   c, v]) = return (ItemByClass c, v)
val2DictEntry pgs (EdhTuple [k, _v]) =
  throwEdhSTM pgs EvalError $ "Invalid key for dict: " <> T.pack (show k)
val2DictEntry pgs val =
  throwEdhSTM pgs EvalError $ "Invalid entry for dict: " <> T.pack (show val)

-- | operator (=>) - prepender
prpdProc :: EdhProcedure
prpdProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit = do
  !pgs <- ask
  evalExpr lhExpr $ \(OriginalValue !lhVal _ _) ->
    evalExpr rhExpr $ \(OriginalValue !rhVal _ _) -> case rhVal of
      EdhTuple vs       -> exitEdhProc exit (EdhTuple $ lhVal : vs)
      EdhList  (List l) -> contEdhSTM $ do
        modifyTVar' l (lhVal :)
        exitEdhSTM pgs exit rhVal
      EdhDict (Dict d) -> contEdhSTM $ do
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
        EdhList (List l) -> contEdhSTM $ edhForLoop
          pgs
          argsRcvr
          iterExpr
          doExpr
          (\val -> modifyTVar' l (++ [val]))
          (\mkLoop -> runEdhProg pgs $ mkLoop $ \_ -> exitEdhProc exit lhVal)
        EdhDict (Dict d) -> contEdhSTM $ edhForLoop
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
          EdhTuple vs'      -> exitEdhProc exit (EdhTuple $ vs ++ vs')
          EdhList  (List l) -> contEdhSTM $ do
            ll <- readTVar l
            exitEdhSTM pgs exit (EdhTuple $ vs ++ ll)
          EdhDict (Dict d) -> contEdhSTM $ do
            ds <- readTVar d
            exitEdhSTM pgs exit (EdhTuple $ vs ++ toPairList ds)
          _ ->
            throwEdh EvalError
              $  "Don't know how to comprehend from a "
              <> T.pack (show $ edhTypeOf rhVal)
              <> ": "
              <> T.pack (show rhVal)
        EdhList (List l) -> case rhVal of
          EdhArgsPack (ArgsPack !args !kwargs) | Map.null kwargs ->
            contEdhSTM $ do
              modifyTVar' l (++ args)
              exitEdhSTM pgs exit lhVal
          EdhTuple vs -> contEdhSTM $ do
            modifyTVar' l (++ vs)
            exitEdhSTM pgs exit lhVal
          EdhList (List l') -> contEdhSTM $ do
            ll <- readTVar l'
            modifyTVar' l (++ ll)
            exitEdhSTM pgs exit lhVal
          EdhDict (Dict d) -> contEdhSTM $ do
            ds <- readTVar d
            modifyTVar' l (++ (toPairList ds))
            exitEdhSTM pgs exit lhVal
          _ ->
            throwEdh EvalError
              $  "Don't know how to comprehend from a "
              <> T.pack (show $ edhTypeOf rhVal)
              <> ": "
              <> T.pack (show rhVal)
        EdhDict (Dict d) -> case rhVal of
          EdhArgsPack (ArgsPack !args !kwargs) | Map.null kwargs ->
            contEdhSTM $ do
              d' <- pvlToDict args
              modifyTVar d $ Map.union d'
              exitEdhSTM pgs exit lhVal
          EdhTuple vs -> contEdhSTM $ do
            d' <- pvlToDict vs
            modifyTVar d $ Map.union d'
            exitEdhSTM pgs exit lhVal
          EdhList (List l) -> contEdhSTM $ do
            ll <- readTVar l
            d' <- pvlToDict ll
            modifyTVar d $ Map.union d'
            exitEdhSTM pgs exit lhVal
          EdhDict (Dict d') -> contEdhSTM $ do
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

