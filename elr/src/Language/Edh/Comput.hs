{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Edh.Comput where

-- import Debug.Trace

import Control.Applicative
import Control.Concurrent.STM
import Control.Monad
import Control.Monad.IO.Class
import Data.Dynamic
import Data.Lossless.Decimal (Decimal)
import qualified Data.Lossless.Decimal as D
import Data.Maybe
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import qualified Data.Text as T
import Data.Unique
import qualified GHC.TypeLits as TypeLits
import Language.Edh.Args
import Language.Edh.Control
import Language.Edh.IOPD
import Language.Edh.InterOpM
import Language.Edh.Monad
import Language.Edh.RtTypes
import Type.Reflection (typeRep)
import Prelude

-- | Scriptable Computation
class ScriptableComput c where
  scriptableArgs :: c -> [ComputArgDecl]

  callByScript :: (?effecting :: Bool) => c -> ArgsPack -> Edh ScriptedResult

  argsScriptedAhead :: c -> KwArgs
  argsScriptedAhead _ = odEmpty

-- | Arg declaration, auto generated intermediate details, to provide meta
-- information to scripting environment
data ComputArgDecl = ComputArgDecl !IfEffectful !AttrKey !TypeName

type IfEffectful = Bool

type TypeName = Text

-- | Scripted Result
data ScriptedResult
  = -- | The computation done with a sole Edh value, though it can be a rather
    -- complex object on its own
    ScriptDone !EdhValue
  | -- | The computation done with a sole host value, and it intends to be
    -- recognizable by general Edh code, even not aware of 'ScriptedResult'
    ScriptDone' !Dynamic
  | -- | Partially applied host computation, with all args ever applied
    forall c.
    (ScriptableComput c, Typeable c) =>
    PartiallyApplied !c ![(ComputArgDecl, EdhValue)]
  | -- | Fully applied host computation, with all args ever applied
    --
    -- It's pending effected yet, thus has to be called again with niladic apk
    -- to take effect. By "taking effect", it'll really resolve effectful
    -- arguments from that call site.
    forall c.
    (ScriptableComput c, Typeable c) =>
    FullyApplied !c ![(ComputArgDecl, EdhValue)]
  | -- | The computation is finally done, with the result as a host value plus
    -- extra named result values, and with all args ever applied
    FullyEffected !Dynamic !KwArgs ![(ComputArgDecl, EdhValue)]

-- | Argument Type that can be adapted from script values
class Typeable a => ComputArgAdapter a where
  adaptedArgType :: Text
  adaptedArgType = T.pack $ show $ typeRep @a

  adaptEdhArg :: EdhValue -> Edh a
  adaptedArgValue :: a -> EdhValue

-- | Scriptable Computation that waiting one more arg to be applied
--
-- this enables currying, by representing partially applied computation as
-- 1st class value
data PendingApplied name a c
  = (TypeLits.KnownSymbol name, ComputArgAdapter a, ScriptableComput c) =>
    PendingApplied !KwArgs !(ComputArg a name -> c)

-- | apply one more arg to a previously saved, partially applied computation
instance
  ( TypeLits.KnownSymbol name,
    ComputArgAdapter a,
    ScriptableComput c,
    Typeable (PendingApplied name a c)
  ) =>
  ScriptableComput (PendingApplied name a c)
  where
  argsScriptedAhead (PendingApplied !pargs _f) = pargs

  scriptableArgs (PendingApplied _pargs !f) = scriptableArgs f

  callByScript (PendingApplied !pargs !f) (ArgsPack !args !kwargs) =
    case odTakeOut argName kwargs of
      (Just !av, !kwargs') -> do
        !ad <- adaptEdhArg av
        callByScript
          (f $ ComputArg ad)
          (ArgsPack args $ odUnion pargs kwargs')
          >>= \case
            ScriptDone !done -> return $ ScriptDone done
            ScriptDone' !done -> return $ ScriptDone' done
            PartiallyApplied c !appliedArgs ->
              return $
                PartiallyApplied c $
                  (argDecl, adaptedArgValue ad) : appliedArgs
            FullyApplied c !appliedArgs ->
              return $
                FullyApplied c $ (argDecl, adaptedArgValue ad) : appliedArgs
            FullyEffected d extras !appliedArgs ->
              return $
                FullyEffected d extras $
                  (argDecl, adaptedArgValue ad) : appliedArgs
      (Nothing, !kwargs') -> case args of
        av : args' -> do
          !ad <- adaptEdhArg av
          callByScript
            (f $ ComputArg ad)
            (ArgsPack args' $ odUnion pargs kwargs')
            >>= \case
              ScriptDone !done -> return $ ScriptDone done
              ScriptDone' !done -> return $ ScriptDone' done
              PartiallyApplied c !appliedArgs ->
                return $
                  PartiallyApplied c $
                    (argDecl, adaptedArgValue ad) : appliedArgs
              FullyApplied c !appliedArgs ->
                return $
                  FullyApplied c $ (argDecl, adaptedArgValue ad) : appliedArgs
              FullyEffected d extras !appliedArgs ->
                return $
                  FullyEffected d extras $
                    (argDecl, adaptedArgValue ad) : appliedArgs
        [] ->
          return $ PartiallyApplied (PendingApplied kwargs' f) []
    where
      argName = AttrByName $ T.pack $ TypeLits.symbolVal (Proxy :: Proxy name)
      argDecl = ComputArgDecl False argName (adaptedArgType @a)

-- | apply one more arg to a scriptable computation
instance
  {-# OVERLAPPABLE #-}
  ( TypeLits.KnownSymbol name,
    ComputArgAdapter a,
    ScriptableComput c,
    Typeable (PendingApplied name a c)
  ) =>
  ScriptableComput (ComputArg a name -> c)
  where
  scriptableArgs f =
    ComputArgDecl False argName (adaptedArgType @a) :
    scriptableArgs (f undefined)
    where
      argName = AttrByName $ T.pack $ TypeLits.symbolVal (Proxy :: Proxy name)

  callByScript f (ArgsPack !args !kwargs) =
    case odTakeOut argName kwargs of
      (Just !av, !kwargs') -> do
        !ad <- adaptEdhArg av
        callByScript (f $ ComputArg ad) (ArgsPack args kwargs') >>= \case
          ScriptDone !done -> return $ ScriptDone done
          ScriptDone' !done -> return $ ScriptDone' done
          PartiallyApplied c !appliedArgs ->
            return $
              PartiallyApplied c $ (argDecl, adaptedArgValue ad) : appliedArgs
          FullyApplied c !appliedArgs ->
            return $
              FullyApplied c $ (argDecl, adaptedArgValue ad) : appliedArgs
          FullyEffected d extras !appliedArgs ->
            return $
              FullyEffected d extras $
                (argDecl, adaptedArgValue ad) : appliedArgs
      (Nothing, !kwargs') -> case args of
        av : args' -> do
          !ad <- adaptEdhArg av
          callByScript (f $ ComputArg ad) (ArgsPack args' kwargs') >>= \case
            ScriptDone !done -> return $ ScriptDone done
            ScriptDone' !done -> return $ ScriptDone' done
            PartiallyApplied c !appliedArgs ->
              return $
                PartiallyApplied c $
                  (argDecl, adaptedArgValue ad) : appliedArgs
            FullyApplied c !appliedArgs ->
              return $
                FullyApplied c $ (argDecl, adaptedArgValue ad) : appliedArgs
            FullyEffected d extras !appliedArgs ->
              return $
                FullyEffected d extras $
                  (argDecl, adaptedArgValue ad) : appliedArgs
        [] ->
          return $ PartiallyApplied (PendingApplied kwargs' f) []
    where
      argName = AttrByName $ T.pack $ TypeLits.symbolVal (Proxy :: Proxy name)
      argDecl = ComputArgDecl False argName (adaptedArgType @a)

-- | Scriptable Computation that waiting to take effect
data PendingMaybeEffected name a c
  = ( TypeLits.KnownSymbol name,
      ComputArgAdapter a,
      ScriptableComput c,
      Typeable (PendingMaybeEffected name a c)
    ) =>
    PendingMaybeEffected !(ComputArg (Effective (Maybe a)) name -> c)

-- | resolve then apply one more effectful arg to previously saved, now
-- effecting computation
instance
  ( TypeLits.KnownSymbol name,
    ComputArgAdapter a,
    ScriptableComput c,
    Typeable (PendingMaybeEffected name a c)
  ) =>
  ScriptableComput (PendingMaybeEffected name a c)
  where
  scriptableArgs (PendingMaybeEffected !f) = scriptableArgs f

  callByScript p@(PendingMaybeEffected !f) (ArgsPack !args !kwargs)
    | not $ null args = throwEdhM UsageError "extranous args"
    | not $ odNull kwargs = throwEdhM UsageError "extranous kwargs"
    | not ?effecting = return $ FullyApplied p []
    | otherwise = applyMaybeEffectfulArg f

-- | resolve then apply one more effectful arg to the effecting computation
instance
  ( TypeLits.KnownSymbol name,
    ComputArgAdapter a,
    ScriptableComput c,
    Typeable (PendingMaybeEffected name a c)
  ) =>
  ScriptableComput (ComputArg (Effective (Maybe a)) name -> c)
  where
  scriptableArgs f =
    ComputArgDecl True argName (T.pack (show $ typeRep @(Maybe a))) :
    scriptableArgs (f undefined)
    where
      argName = AttrByName $ T.pack $ TypeLits.symbolVal (Proxy :: Proxy name)

  callByScript !f (ArgsPack !args !kwargs)
    | not $ null args = throwEdhM UsageError "extranous args"
    | not $ odNull kwargs = throwEdhM UsageError "extranous kwargs"
    | not ?effecting = return $ FullyApplied (PendingMaybeEffected f) []
    | otherwise = applyMaybeEffectfulArg f

-- | resolve then apply one more effectful arg to the effecting computation
applyMaybeEffectfulArg ::
  forall name a c.
  (TypeLits.KnownSymbol name, ComputArgAdapter a, ScriptableComput c) =>
  (ComputArg (Effective (Maybe a)) name -> c) ->
  Edh ScriptedResult
applyMaybeEffectfulArg !f = do
  !maybeVal <- performM' argName
  let ?effecting = True
   in case maybeVal of
        Nothing ->
          callByScript
            (f $ ComputArg $ Effective Nothing)
            (ArgsPack [] odEmpty)
            >>= \case
              ScriptDone !done -> return $ ScriptDone done
              ScriptDone' !done -> return $ ScriptDone' done
              FullyEffected d extras !appliedArgs ->
                return $ FullyEffected d extras appliedArgs
              _ -> throwEdhM EvalError "bug: not fully effected"
        Just !av -> do
          !ad <- adaptEdhArg av
          callByScript
            (f $ ComputArg $ Effective $ Just ad)
            (ArgsPack [] odEmpty)
            >>= \case
              ScriptDone !done -> return $ ScriptDone done
              ScriptDone' !done -> return $ ScriptDone' done
              FullyEffected d extras !appliedArgs ->
                return $
                  FullyEffected d extras $
                    (argDecl, adaptedArgValue ad) : appliedArgs
              _ -> throwEdhM EvalError "bug: not fully effected"
  where
    argName = AttrByName $ T.pack $ TypeLits.symbolVal (Proxy :: Proxy name)
    argDecl = ComputArgDecl True argName (T.pack $ show $ typeRep @(Maybe a))

-- | Scriptable Computation that waiting to take effect
data PendingEffected name a c
  = (TypeLits.KnownSymbol name, ComputArgAdapter a, ScriptableComput c) =>
    PendingEffected !(ComputArg (Effective a) name -> c)

-- | resolve then apply one more effectful arg to previously saved, now
-- effecting computation
instance
  ( TypeLits.KnownSymbol name,
    ComputArgAdapter a,
    ScriptableComput c,
    Typeable (PendingEffected name a c)
  ) =>
  ScriptableComput (PendingEffected name a c)
  where
  scriptableArgs (PendingEffected !f) = scriptableArgs f

  callByScript p@(PendingEffected !f) (ArgsPack !args !kwargs)
    | not $ null args = throwEdhM UsageError "extranous args"
    | not $ odNull kwargs = throwEdhM UsageError "extranous kwargs"
    | not ?effecting = return $ FullyApplied p []
    | otherwise = applyEffectfulArg f

-- | resolve then apply one more effectful arg to the effecting computation
instance
  {-# OVERLAPPABLE #-}
  ( TypeLits.KnownSymbol name,
    ComputArgAdapter a,
    ScriptableComput c,
    Typeable (PendingEffected name a c)
  ) =>
  ScriptableComput (ComputArg (Effective a) name -> c)
  where
  scriptableArgs f =
    ComputArgDecl True argName (T.pack $ show $ typeRep @a) :
    scriptableArgs (f undefined)
    where
      argName = AttrByName $ T.pack $ TypeLits.symbolVal (Proxy :: Proxy name)

  callByScript !f (ArgsPack !args !kwargs)
    | not $ null args = throwEdhM UsageError "extranous args"
    | not $ odNull kwargs = throwEdhM UsageError "extranous kwargs"
    | not ?effecting = return $ FullyApplied (PendingEffected f) []
    | otherwise = applyEffectfulArg f

-- | resolve then apply one more effectful arg to the effecting computation
applyEffectfulArg ::
  forall name a c.
  (TypeLits.KnownSymbol name, ComputArgAdapter a, ScriptableComput c) =>
  (ComputArg (Effective a) name -> c) ->
  Edh ScriptedResult
applyEffectfulArg !f = do
  !maybeVal <- performM' argName
  let ?effecting = True
   in case maybeVal of
        Nothing ->
          throwEdhM UsageError $
            "missing effectful arg: " <> attrKeyStr argName
        Just !av -> do
          !ad <- adaptEdhArg av
          callByScript
            (f $ ComputArg $ Effective ad)
            (ArgsPack [] odEmpty)
            >>= \case
              ScriptDone !done -> return $ ScriptDone done
              ScriptDone' !done -> return $ ScriptDone' done
              FullyEffected d extras !appliedArgs ->
                return $
                  FullyEffected d extras $
                    (argDecl, adaptedArgValue ad) : appliedArgs
              _ -> error "bug: not fully effected"
  where
    argName = AttrByName $ T.pack $ TypeLits.symbolVal (Proxy :: Proxy name)
    argDecl = ComputArgDecl True argName (T.pack $ show $ typeRep @a)

-- * Computation result as base cases

-- | Pure computation result as scripted, without recording all args ever
-- applied
instance ScriptableComput EdhValue where
  scriptableArgs _ = []
  callByScript v (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else return $ ScriptDone v

-- | Wrap a pure computation result as scripted, without recording of all args
-- ever applied
data ComputDone a = (Typeable a) => ComputDone !a

instance ScriptableComput (ComputDone a) where
  scriptableArgs _ = []
  callByScript (ComputDone a) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else return $ ScriptDone' (toDyn a)

-- | Wrap a pure computation result as scripted
data ComputPure a = (Typeable a) => ComputPure !a

instance ScriptableComput (ComputPure a) where
  scriptableArgs _ = []
  callByScript (ComputPure a) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else return $ FullyEffected (toDyn a) odEmpty []

-- | Edh aware computation result as scripted
instance ScriptableComput (Edh Dynamic) where
  scriptableArgs _ = []

  callByScript !act (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else (<$> act) $ \ !d -> FullyEffected d odEmpty []

-- | Edh aware computation result as scripted
instance {-# OVERLAPPABLE #-} Typeable a => ScriptableComput (Edh a) where
  scriptableArgs _ = []

  callByScript !act (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else (<$> act) $ \ !a -> FullyEffected (toDyn a) odEmpty []

-- | Edh aware computation result as scripted, without recording all args ever
-- applied
instance ScriptableComput (Edh EdhValue) where
  scriptableArgs _ = []

  callByScript !act (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else ScriptDone <$> act

-- | Wrap an Edh aware computation result as scripted, and you would give out
-- one or more named results in addition, those can be separately obtained by
-- the script at will
data InflateEdh a = Typeable a => InflateEdh (Edh (a, KwArgs))

instance ScriptableComput (InflateEdh a) where
  scriptableArgs _ = []

  callByScript (InflateEdh !act) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else (<$> act) $ \(!d, !extras) ->
        FullyEffected (toDyn d) extras []

-- | Wrap an Edh aware computation result as scripted, and you would give out
-- one or more named results in addition, those can be separately obtained by
-- the script at will
--
-- Use this form in case you construct a 'Dynamic' result yourself
newtype InflateEdh' a = InflateEdh' (Edh (Dynamic, KwArgs))

instance ScriptableComput (InflateEdh' a) where
  scriptableArgs _ = []

  callByScript (InflateEdh' !act) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else (<$> act) $ \(!d, !extras) ->
        FullyEffected d extras []

-- | Wrap a scripted general computation in the 'EIO' monad
data ComputEIO a = Typeable a => ComputEIO (EIO a)

instance ScriptableComput (ComputEIO a) where
  scriptableArgs _ = []

  callByScript (ComputEIO !act) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else (<$> liftEIO act) $ \ !d -> FullyEffected (toDyn d) odEmpty []

-- | Wrap a scripted general computation in the 'EIO' monad
--
-- Use this form in case you construct a 'Dynamic' result yourself
--
-- Note the type @a@ is for information purpose only, no way get asserted
data ComputEIO' a = Typeable a => ComputEIO' (EIO Dynamic)

instance ScriptableComput (ComputEIO' a) where
  scriptableArgs _ = []

  callByScript (ComputEIO' !act) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else (<$> liftEIO act) $ \ !d -> FullyEffected d odEmpty []

-- | Wrap a scripted general computation in the 'EIO' monad, without recording
-- all args ever applied
--
-- Use this form in case you can give out an 'EdhValue' directly
newtype ComputEIO_ = ComputEIO_ (EIO EdhValue)

instance ScriptableComput ComputEIO_ where
  scriptableArgs _ = []

  callByScript (ComputEIO_ !act) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else ScriptDone <$> liftEIO act

-- | Wrap a scripted general computation in the 'IO' monad
data ComputIO a = Typeable a => ComputIO (IO a)

instance ScriptableComput (ComputIO a) where
  scriptableArgs _ = []

  callByScript (ComputIO !act) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else (<$> liftIO act) $ \ !d -> FullyEffected (toDyn d) odEmpty []

-- | Wrap a scripted general computation in the 'IO' monad
--
-- Use this form in case you construct a 'Dynamic' result yourself
--
-- Note the type @a@ is for information purpose only, no way get asserted
data ComputIO' a = Typeable a => ComputIO' (IO Dynamic)

instance ScriptableComput (ComputIO' a) where
  scriptableArgs _ = []

  callByScript (ComputIO' !act) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else (<$> liftIO act) $ \ !d -> FullyEffected d odEmpty []

-- | Wrap a scripted general computation in the 'IO' monad, without recording
-- all args ever applied
--
-- Use this form in case you can give out an 'EdhValue' directly
newtype ComputIO_ = ComputIO_ (IO EdhValue)

instance ScriptableComput ComputIO_ where
  scriptableArgs _ = []

  callByScript (ComputIO_ !act) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else ScriptDone <$> liftIO act

-- | Wrap a scripted general computation in the 'STM' monad
data ComputSTM a = Typeable a => ComputSTM (STM a)

instance ScriptableComput (ComputSTM a) where
  scriptableArgs _ = []

  callByScript (ComputSTM !act) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else (<$> liftSTM act) $ \ !d -> FullyEffected (toDyn d) odEmpty []

-- | Wrap a scripted general computation in the 'STM' monad
--
-- Use this form in case you construct a 'Dynamic' result yourself
--
-- Note the type @a@ is for information purpose only, no way get asserted
newtype ComputSTM' a = ComputSTM' (STM Dynamic)

instance ScriptableComput (ComputSTM' a) where
  scriptableArgs _ = []

  callByScript (ComputSTM' !act) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else (<$> liftSTM act) $ \ !d -> FullyEffected d odEmpty []

-- | Wrap a scripted general computation in the 'STM' monad, without recording
-- all args ever applied
--
-- Use this form in case you can give out an 'EdhValue' directly
newtype ComputSTM_ = ComputSTM_ (STM EdhValue)

instance ScriptableComput ComputSTM_ where
  scriptableArgs _ = []

  callByScript (ComputSTM_ !act) (ArgsPack !args !kwargs) =
    if not (null args) || not (odNull kwargs)
      then throwEdhM UsageError "extranous arguments"
      else ScriptDone <$> liftSTM act

-- * Script Argument Adapters

instance ComputArgAdapter EdhValue where
  adaptEdhArg !v = return v
  adaptedArgValue = id

instance ComputArgAdapter (Maybe Object) where
  adaptEdhArg !v = case edhUltimate v of
    EdhNil -> return Nothing
    EdhObject !d -> return $ Just d
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            "optional "
              <> adaptedArgType @Object
              <> " expected but given: "
              <> badDesc
  adaptedArgValue (Just !d) = EdhObject d
  adaptedArgValue Nothing = edhNothing

instance ComputArgAdapter Object where
  adaptEdhArg !v = case edhUltimate v of
    EdhObject !d -> return d
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            adaptedArgType @Object <> " expected but given: " <> badDesc
  adaptedArgValue = EdhObject

instance ComputArgAdapter (Maybe Decimal) where
  adaptEdhArg !v = case edhUltimate v of
    EdhNil -> return Nothing
    EdhDecimal !d -> return $ Just d
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            "optional "
              <> adaptedArgType @Decimal
              <> " expected but given: "
              <> badDesc
  adaptedArgValue (Just !d) = EdhDecimal d
  adaptedArgValue Nothing = edhNothing

instance ComputArgAdapter Decimal where
  adaptEdhArg !v = case edhUltimate v of
    EdhDecimal !d -> return d
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            adaptedArgType @Decimal <> " expected but given: " <> badDesc
  adaptedArgValue = EdhDecimal

instance ComputArgAdapter (Maybe Double) where
  adaptEdhArg !v = case edhUltimate v of
    EdhNil -> return Nothing
    EdhDecimal !d -> return $ Just $ D.decimalToRealFloat d
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            "optional " <> adaptedArgType @Double
              <> " expected but given: "
              <> badDesc
  adaptedArgValue (Just !d) = EdhDecimal $ D.decimalFromRealFloat d
  adaptedArgValue Nothing = edhNothing

instance ComputArgAdapter Double where
  adaptEdhArg !v = case edhUltimate v of
    EdhDecimal !d -> return $ D.decimalToRealFloat d
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            adaptedArgType @Double <> " expected but given: " <> badDesc
  adaptedArgValue = EdhDecimal . D.decimalFromRealFloat

instance
  {-# OVERLAPPABLE #-}
  forall i.
  (Typeable i, Integral i) =>
  ComputArgAdapter (Maybe i)
  where
  adaptEdhArg !v = case edhUltimate v of
    EdhNil -> return Nothing
    EdhDecimal !d -> case D.decimalToInteger d of
      Just !i -> return $ Just $ fromInteger i
      Nothing -> badVal
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            "optional " <> adaptedArgType @i
              <> " expected but given: "
              <> badDesc
  adaptedArgValue (Just !i) = EdhDecimal $ fromIntegral i
  adaptedArgValue Nothing = edhNothing

instance
  {-# OVERLAPPABLE #-}
  forall i.
  (Typeable i, Integral i) =>
  ComputArgAdapter i
  where
  adaptEdhArg !v = case edhUltimate v of
    EdhDecimal !d -> case D.decimalToInteger d of
      Just !i -> return $ fromInteger i
      Nothing -> badVal
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            adaptedArgType @i <> " expected but given: " <> badDesc
  adaptedArgValue !i = EdhDecimal $ fromIntegral i

newtype Count = Count Int
  deriving (Eq, Ord, Enum, Num, Real, Integral, Show)

instance ComputArgAdapter (Maybe Count) where
  adaptEdhArg !v = case edhUltimate v of
    EdhNil -> return Nothing
    EdhDecimal !d | d >= 1 -> case D.decimalToInteger d of
      Just !i -> return $ Just $ Count $ fromInteger i
      Nothing -> badVal
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            adaptedArgType @Count
              <> " (positive integer) expected but given: "
              <> badDesc
  adaptedArgValue (Just (Count !i)) = EdhDecimal $ fromIntegral i
  adaptedArgValue Nothing = edhNothing

instance ComputArgAdapter Count where
  adaptEdhArg !v = case edhUltimate v of
    EdhDecimal !d | d >= 1 -> case D.decimalToInteger d of
      Just !i -> return $ Count $ fromInteger i
      Nothing -> badVal
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            adaptedArgType @Count
              <> " (positive integer) expected but given: "
              <> badDesc
  adaptedArgValue (Count !i) = EdhDecimal $ fromIntegral i

data HostData (tn :: TypeLits.Symbol) = HostData !Dynamic !Object

instance
  TypeLits.KnownSymbol tn =>
  ComputArgAdapter (Maybe (HostData tn))
  where
  adaptedArgType = T.pack $ "Maybe " <> TypeLits.symbolVal (Proxy :: Proxy tn)

  adaptEdhArg !v = case edhUltimate v of
    EdhNil -> return Nothing
    EdhObject o -> case edh'obj'store o of
      HostStore dd -> case fromDynamic dd of
        Just (sr :: ScriptedResult) -> case sr of
          ScriptDone' d -> return $ Just $ HostData d o
          FullyEffected d _extras _applied ->
            return $ Just $ HostData d o
          _ -> return $ Just $ HostData dd o
        Nothing -> return $ Just $ HostData dd o
      _ -> badVal
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            adaptedArgType @(HostData tn) <> " expected but given: " <> badDesc

  adaptedArgValue (Just (HostData _dd !obj)) = EdhObject obj
  adaptedArgValue Nothing = edhNothing

instance TypeLits.KnownSymbol tn => ComputArgAdapter (HostData tn) where
  adaptedArgType = T.pack $ TypeLits.symbolVal (Proxy :: Proxy tn)

  adaptEdhArg !v = case edhUltimate v of
    EdhObject o -> case edh'obj'store o of
      HostStore dd -> case fromDynamic dd of
        Just (sr :: ScriptedResult) -> case sr of
          ScriptDone' d -> return $ HostData d o
          FullyEffected d _extras _applied -> return $ HostData d o
          _ -> return $ HostData dd o
        Nothing -> return $ HostData dd o
      _ -> badVal
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            adaptedArgType @(HostData tn) <> " expected but given: " <> badDesc

  adaptedArgValue (HostData _dd !obj) = EdhObject obj

data HostValue t = Typeable t => HostValue !t !Object

instance Typeable t => ComputArgAdapter (Maybe (HostValue t)) where
  adaptedArgType = T.pack $ "Maybe " <> show (typeRep @t)

  adaptEdhArg !v = case edhUltimate v of
    EdhNil -> return Nothing
    EdhObject o -> case edh'obj'store o of
      HostStore dd -> case fromDynamic dd of
        Just (sr :: ScriptedResult) -> case sr of
          ScriptDone' d -> case fromDynamic d of
            Just (t :: t) -> return $ Just $ HostValue t o
            Nothing -> badVal
          FullyEffected d _extras _applied -> case fromDynamic d of
            Just (t :: t) -> return $ Just $ HostValue t o
            Nothing -> badVal
          _ -> badVal
        Nothing -> case fromDynamic dd of
          Just (t :: t) -> return $ Just $ HostValue t o
          Nothing -> badVal
      _ -> badVal
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            adaptedArgType @(HostValue t) <> " expected but given: " <> badDesc

  adaptedArgValue (Just (HostValue _val !obj)) = EdhObject obj
  adaptedArgValue Nothing = edhNothing

instance Typeable t => ComputArgAdapter (HostValue t) where
  adaptedArgType = T.pack $ show $ typeRep @t

  adaptEdhArg !v = case edhUltimate v of
    EdhObject o -> case edh'obj'store o of
      HostStore dd -> case fromDynamic dd of
        Just (sr :: ScriptedResult) -> case sr of
          ScriptDone' d -> case fromDynamic d of
            Just (t :: t) -> return $ HostValue t o
            Nothing -> badVal
          FullyEffected d _extras _applied -> case fromDynamic d of
            Just (t :: t) -> return $ HostValue t o
            Nothing -> badVal
          _ -> badVal
        Nothing -> case fromDynamic dd of
          Just (t :: t) -> return $ HostValue t o
          Nothing -> badVal
      _ -> badVal
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            adaptedArgType @(HostValue t) <> " expected but given: " <> badDesc

  adaptedArgValue (HostValue _val !obj) = EdhObject obj

data HostSeq t = ComputArgAdapter t => HostSeq ![t] ![EdhValue]

instance (Typeable t, ComputArgAdapter t) => ComputArgAdapter (HostSeq t) where
  adaptedArgType = T.pack $ "[" <> show (typeRep @t) <> "]"

  adaptEdhArg !v = case edhUltimate v of
    EdhArgsPack (ArgsPack !args !kwargs)
      | odNull kwargs -> exitWith args
    EdhList (List _u !lv) -> exitWith =<< readTVarEdh lv
    _ -> badVal
    where
      badVal =
        edhSimpleDescM v >>= \ !badDesc ->
          throwEdhM UsageError $
            adaptedArgType @(HostSeq t) <> " expected but given: " <> badDesc
      exitWith :: [EdhValue] -> Edh (HostSeq t)
      exitWith [] = return $ HostSeq [] []
      exitWith !vs = go vs []
        where
          go :: [EdhValue] -> [(t, EdhValue)] -> Edh (HostSeq t)
          go [] rs = return $ uncurry HostSeq $ unzip $ reverse rs
          go (ev : rest) rs =
            adaptEdhArg ev >>= \ !t -> go rest ((t, adaptedArgValue t) : rs)

  adaptedArgValue (HostSeq _vals !edhVals) =
    EdhArgsPack $ ArgsPack edhVals odEmpty

-- * Utilities

-- providing argument default value, by constructing object of the designated
-- comput class

appliedArgWithDefaultCtor ::
  forall t name.
  Typeable t =>
  EdhValue ->
  ComputArg (Maybe (HostValue t)) name ->
  Edh t
appliedArgWithDefaultCtor = appliedArgWithDefaultCtor' []

appliedArgWithDefaultCtor' ::
  forall t name.
  Typeable t =>
  [EdhValue] ->
  EdhValue ->
  ComputArg (Maybe (HostValue t)) name ->
  Edh t
appliedArgWithDefaultCtor' = flip appliedArgWithDefaultCtor'' []

appliedArgWithDefaultCtor'' ::
  forall t name.
  Typeable t =>
  [EdhValue] ->
  [(AttrKey, EdhValue)] ->
  EdhValue ->
  ComputArg (Maybe (HostValue t)) name ->
  Edh t
appliedArgWithDefaultCtor''
  !args
  !kwargs
  !callee
  (appliedArg -> !maybeHostVal) =
    case maybeHostVal of
      Just (HostValue (t :: t) _obj) -> return t
      Nothing -> do
        !val <- callM' callee (ArgsPack args $ odFromList kwargs)
        let badArg =
              edhSimpleDescM val >>= \ !badDesc ->
                throwEdhM UsageError $
                  "bug: wrong host value constructed as default for "
                    <> T.pack (show $ typeRep @t)
                    <> ": "
                    <> badDesc
        case edhUltimate val of
          EdhObject !o -> case edh'obj'store o of
            HostStore dd -> case fromDynamic dd of
              Just (sr :: ScriptedResult) -> case sr of
                FullyEffected d _extras _applied -> case fromDynamic d of
                  Just (t :: t) -> return t
                  Nothing -> badArg
                _ -> badArg
              Nothing -> case fromDynamic dd of
                Just (t :: t) -> return t
                Nothing -> badArg
            _ -> badArg
          _ -> badArg

effectfulArgWithDefaultCtor ::
  forall t name.
  Typeable t =>
  EdhValue ->
  ComputArg (Effective (Maybe (HostValue t))) name ->
  Edh (t, Object)
effectfulArgWithDefaultCtor = effectfulArgWithDefaultCtor' []

effectfulArgWithDefaultCtor' ::
  forall t name.
  Typeable t =>
  [EdhValue] ->
  EdhValue ->
  ComputArg (Effective (Maybe (HostValue t))) name ->
  Edh (t, Object)
effectfulArgWithDefaultCtor' = flip effectfulArgWithDefaultCtor'' []

effectfulArgWithDefaultCtor'' ::
  forall t name.
  Typeable t =>
  [EdhValue] ->
  [(AttrKey, EdhValue)] ->
  EdhValue ->
  ComputArg (Effective (Maybe (HostValue t))) name ->
  Edh (t, Object)
effectfulArgWithDefaultCtor''
  !args
  !kwargs
  !callee
  (effectfulArg -> !maybeVal) =
    case maybeVal of
      Just (HostValue (t :: t) o) -> return (t, o)
      Nothing -> do
        !val <- callM' callee (ArgsPack args $ odFromList kwargs)
        let badArg =
              edhSimpleDescM val >>= \ !badDesc ->
                throwEdhM UsageError $
                  "bug: wrong host value constructed as default for "
                    <> T.pack (show $ typeRep @t)
                    <> ": "
                    <> badDesc
        case edhUltimate val of
          EdhObject !o -> case edh'obj'store o of
            HostStore dd -> case fromDynamic dd of
              Just (sr :: ScriptedResult) -> case sr of
                FullyEffected d _extras _applied -> case fromDynamic d of
                  Just (t :: t) -> return (t, o)
                  Nothing -> badArg
                _ -> badArg
              Nothing -> case fromDynamic dd of
                Just (t :: t) -> return (t, o)
                Nothing -> badArg
            _ -> badArg
          _ -> badArg

-- * Defining Methods/Classes for Curried Host Computation

defineComputMethod ::
  forall c.
  (Typeable c, ScriptableComput c) =>
  c ->
  AttrName ->
  Edh EdhValue
defineComputMethod !comput !mthName =
  mkEdhProc EdhMethod mthName (mthProc, argsRcvr)
  where
    mthProc :: ArgsPack -> Edh EdhValue
    mthProc !apk =
      let ?effecting = True
       in callByScript comput apk >>= \ !sr -> case sr of
            ScriptDone !done -> return done
            ScriptDone' !done -> do
              !apkRepr <- edhValueReprM $ EdhArgsPack apk
              EdhObject <$> wrapM'' (mthName <> apkRepr) done
            PartiallyApplied c appliedArgs -> do
              !argsRepr <- tshowAppliedArgs appliedArgs
              !argsAheadRepr <- tshowArgsAhead $ odToList $ argsScriptedAhead c
              defineComputMethod
                c
                (mthName <> "( " <> argsRepr <> argsAheadRepr <> ")")
            FullyApplied c appliedArgs -> do
              !argsRepr <- tshowAppliedArgs appliedArgs
              defineComputMethod
                c
                (mthName <> "( " <> argsRepr <> ")")
            FullyEffected !d _extras _appliedArgs -> do
              !apkRepr <- edhValueReprM $ EdhArgsPack apk
              EdhObject <$> wrapM'' (mthName <> apkRepr) d

    argsRcvr :: ArgsReceiver
    argsRcvr = NullaryReceiver -- TODO infer from scriptableArgs

    --
    tshowAppliedArgs :: [(ComputArgDecl, EdhValue)] -> Edh Text
    tshowAppliedArgs [] = return ""
    tshowAppliedArgs ((ComputArgDecl !eff !k _type, !v) : rest) = do
      !restRepr <- tshowAppliedArgs rest
      !repr <- edhValueReprM v
      return $
        (if eff then "effect " else "") <> attrKeyStr k <> "= " <> repr
          <> ", "
          <> restRepr

    tshowArgsAhead :: [(AttrKey, EdhValue)] -> Edh Text
    tshowArgsAhead [] = return ""
    tshowArgsAhead ((!k, !v) : rest) = do
      !restRepr <- tshowArgsAhead rest
      !repr <- edhValueReprM v
      return $ attrKeyStr k <> "= " <> repr <> ", " <> restRepr

defineComputClass ::
  forall c.
  (ScriptableComput c, Typeable c) =>
  c ->
  AttrName ->
  Edh Object
defineComputClass = defineComputClass' True

type EffectOnCtor = Bool

defineComputClass' ::
  forall c.
  (ScriptableComput c, Typeable c) =>
  EffectOnCtor ->
  c ->
  AttrName ->
  Edh Object
defineComputClass' !effOnCtor !rootComput !clsName =
  mkEdhClass clsName computAllocator [] $ do
    !ets <- edhThreadState
    let !clsScope = contextScope $ edh'context ets
    !mths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ("(@)", EdhMethod, wrapEdhProc attrReadProc),
                ("([])", EdhMethod, wrapEdhProc attrReadProc),
                ("__repr__", EdhMethod, wrapEdhProc reprProc),
                ("__show__", EdhMethod, wrapEdhProc showProc),
                ("__call__", EdhMethod, wrapEdhProc callProc)
              ]
        ]
    inlineSTM $ iopdUpdate mths $ edh'scope'entity clsScope
  where
    computAllocator :: ArgsPack -> Edh (Maybe Unique, ObjectStore)
    computAllocator !apk =
      let ?effecting = effOnCtor
       in callByScript rootComput apk >>= \ !sr ->
            return (Nothing, HostStore $ toDyn sr)

    -- Obtain an applied argument or a result field by name
    attrReadProc :: EdhValue -> Edh EdhValue
    attrReadProc !keyVal = do
      !argKey <- edhValueAsAttrKeyM keyVal
      (<|> rawValue) $
        thisScripted >>= \case
          ScriptDone {} -> return nil
          ScriptDone' {} -> return nil
          PartiallyApplied _c appliedArgs ->
            return $ appliedArgByKey argKey appliedArgs
          FullyApplied _c appliedArgs ->
            return $ appliedArgByKey argKey appliedArgs
          FullyEffected _d !extras appliedArgs -> case odLookup argKey extras of
            Just !val -> return val
            Nothing -> return $ appliedArgByKey argKey appliedArgs
      where
        rawValue :: Edh EdhValue
        rawValue = case edhUltimate keyVal of
          EdhString "self" ->
            EdhObject . edh'scope'that . contextScope . edh'context
              <$> edhThreadState
          _ -> return nil

    reprProc :: ArgsPack -> Edh EdhValue
    reprProc _ =
      (<|> rawValue) $
        thisScripted >>= \case
          ScriptDone !done ->
            edhValueReprM done >>= \ !doneRepr ->
              return $ EdhString $ "{# " <> clsName <> " #} " <> doneRepr
          ScriptDone' !dd ->
            return $
              EdhString $ "{# " <> clsName <> ": " <> T.pack (show dd) <> " #} "
          PartiallyApplied c appliedArgs -> do
            !appliedArgsRepr <- tshowAppliedArgs appliedArgs
            !argsAheadRepr <- tshowArgsAhead (odToList $ argsScriptedAhead c)
            !moreArgsRepr <- tshowMoreArgs (scriptableArgs c)
            return $
              EdhString $
                clsName <> "( " <> appliedArgsRepr <> argsAheadRepr
                  <> ") {# "
                  <> moreArgsRepr
                  <> "#}"
          FullyApplied c appliedArgs -> do
            !appliedArgsRepr <- tshowAppliedArgs appliedArgs
            !moreArgsRepr <- tshowMoreArgs (scriptableArgs c)
            return $
              EdhString $
                clsName <> "( " <> appliedArgsRepr <> ") {# "
                  <> moreArgsRepr
                  <> "#}"
          FullyEffected _d extras appliedArgs -> do
            !appliedArgsRepr <- tshowAppliedArgs appliedArgs
            !extrasRepr <- tshowExtras (odToList extras)
            return $
              EdhString $
                clsName <> "( " <> appliedArgsRepr <> ") {# "
                  <> extrasRepr
                  <> "#}"
      where
        rawValue :: Edh EdhValue
        rawValue = do
          !this <-
            edh'scope'this . contextScope . edh'context <$> edhThreadState
          case edh'obj'store this of
            HostStore (Dynamic tr _) ->
              return $
                EdhString $
                  "{# " <> clsName <> ": <raw:" <> T.pack (show tr) <> "> #} "
            _ -> throwEdhM EvalError "bug: Comput not a host object"

        tshowAppliedArgs ::
          [(ComputArgDecl, EdhValue)] -> Edh Text
        tshowAppliedArgs [] = return ""
        tshowAppliedArgs ((ComputArgDecl !eff !k _type, !v) : rest) = do
          !restRepr <- tshowAppliedArgs rest
          !repr <- edhValueReprM v
          return $
            (if eff then "effect " else "")
              <> attrKeyStr k
              <> "= "
              <> repr
              <> ", "
              <> restRepr

        tshowArgsAhead ::
          [(AttrKey, EdhValue)] -> Edh Text
        tshowArgsAhead [] = return ""
        tshowArgsAhead ((!k, !v) : rest) = do
          !restRepr <- tshowArgsAhead rest
          !repr <- edhValueReprM v
          return $
            attrKeyStr k <> "= " <> repr <> ", " <> restRepr

        tshowMoreArgs :: [ComputArgDecl] -> Edh Text
        tshowMoreArgs [] = return ""
        tshowMoreArgs (ComputArgDecl !eff !k !typeName : rest) = do
          !restRepr <- tshowMoreArgs rest
          return $
            (if eff then "effect " else "")
              <> attrKeyStr k
              <> " :: "
              <> typeName
              <> ", "
              <> restRepr

        tshowExtras ::
          [(AttrKey, EdhValue)] -> Edh Text
        tshowExtras [] = return ""
        tshowExtras ((!k, !v) : rest) = do
          !restRepr <- tshowExtras rest
          !repr <- edhValueReprM v
          return $
            attrKeyStr k
              <> "= "
              <> repr
              <> ", "
              <> restRepr

    showProc :: ArgsPack -> Edh EdhValue
    showProc _ =
      (<|> rawValue) $
        thisScripted >>= \case
          ScriptDone !done ->
            edhValueReprM done >>= \ !doneRepr ->
              return $
                EdhString $ clsName <> ": <done> " <> doneRepr
          ScriptDone' !dd ->
            return $
              EdhString $ clsName <> ": <host> " <> T.pack (show dd)
          PartiallyApplied c appliedArgs -> do
            !appliedArgsRepr <- tshowAppliedArgs appliedArgs
            !argsAheadRepr <- tshowArgsAhead (odToList $ argsScriptedAhead c)
            !moreArgsRepr <- tshowMoreArgs (scriptableArgs c)
            return $
              EdhString $
                clsName <> "(\n" <> appliedArgsRepr <> argsAheadRepr
                  <> "\n) {#\n"
                  <> moreArgsRepr
                  <> "\n#}"
          FullyApplied c appliedArgs -> do
            !appliedArgsRepr <- tshowAppliedArgs appliedArgs
            !moreArgsRepr <- tshowMoreArgs (scriptableArgs c)
            return $
              EdhString $
                clsName <> "(\n" <> appliedArgsRepr <> "\n) {#\n"
                  <> moreArgsRepr
                  <> "\n#}"
          FullyEffected _d extras appliedArgs -> do
            !appliedArgsRepr <- tshowAppliedArgs appliedArgs
            !extrasRepr <- tshowExtras (odToList extras)
            return $
              EdhString $
                clsName <> "(\n" <> appliedArgsRepr <> "\n) {#\n"
                  <> extrasRepr
                  <> "\n#}"
      where
        rawValue :: Edh EdhValue
        rawValue = do
          !this <-
            edh'scope'this . contextScope . edh'context <$> edhThreadState
          case edh'obj'store this of
            HostStore (Dynamic tr _) ->
              return $ EdhString $ clsName <> ": <raw:" <> T.pack (show tr)
            _ -> throwEdhM EvalError "bug: Comput not a host object"

        tshowAppliedArgs ::
          [(ComputArgDecl, EdhValue)] -> Edh Text
        tshowAppliedArgs [] = return ""
        tshowAppliedArgs ((ComputArgDecl !eff !k _type, !v) : rest) = do
          !restRepr <- tshowAppliedArgs rest
          !repr <- edhValueReprM v
          return $
            (if eff then "  effect " else "  ")
              <> attrKeyStr k
              <> "= "
              <> repr
              <> ",\n"
              <> restRepr

        tshowArgsAhead ::
          [(AttrKey, EdhValue)] -> Edh Text
        tshowArgsAhead [] = return ""
        tshowArgsAhead ((!k, !v) : rest) = do
          !restRepr <- tshowArgsAhead rest
          !repr <- edhValueReprM v
          return $ "  " <> attrKeyStr k <> "= " <> repr <> ",\n" <> restRepr

        tshowMoreArgs :: [ComputArgDecl] -> Edh Text
        tshowMoreArgs [] = return ""
        tshowMoreArgs (ComputArgDecl !eff !k !typeName : rest) = do
          !restRepr <- tshowMoreArgs rest
          return $
            (if eff then "  effect " else "  ")
              <> attrKeyStr k
              <> " :: "
              <> typeName
              <> ",\n"
              <> restRepr

        tshowExtras ::
          [(AttrKey, EdhValue)] -> Edh Text
        tshowExtras [] = return ""
        tshowExtras ((!k, !v) : rest) = do
          !restRepr <- tshowExtras rest
          !repr <- edhValueReprM v
          return $ "  " <> attrKeyStr k <> "= " <> repr <> ",\n" <> restRepr

    callProc :: ArgsPack -> Edh EdhValue
    callProc apk@(ArgsPack args kwargs) =
      thisScripted >>= \case
        ScriptDone !done ->
          if null args && odNull kwargs
            then return done
            else throwEdhM UsageError "extranous arguments"
        ScriptDone' {} ->
          if null args && odNull kwargs
            then
              EdhObject . edh'scope'that . contextScope . edh'context
                <$> edhThreadState
            else throwEdhM UsageError "extranous arguments"
        PartiallyApplied c appliedArgs ->
          let ?effecting = True
           in callByScript c apk >>= exitWith appliedArgs
        FullyApplied c appliedArgs ->
          let ?effecting = True
           in callByScript c apk >>= exitWith appliedArgs
        FullyEffected {} ->
          if null args && odNull kwargs
            then
              EdhObject . edh'scope'that . contextScope . edh'context
                <$> edhThreadState
            else throwEdhM UsageError "extranous arguments"
      where
        exitWith ::
          [(ComputArgDecl, EdhValue)] -> ScriptedResult -> Edh EdhValue
        exitWith appliedArgs sr = case sr of
          ScriptDone !done -> return done
          ScriptDone' !dd ->
            EdhObject
              <$> wrapM''
                ("<" <> clsName <> "/done:" <> T.pack (show dd) <> ">")
                dd
          PartiallyApplied c' appliedArgs' ->
            exitDerived $
              toDyn $ PartiallyApplied c' $! appliedArgs ++ appliedArgs'
          FullyApplied c' appliedArgs' ->
            exitDerived $
              toDyn $ FullyApplied c' $! appliedArgs ++ appliedArgs'
          FullyEffected !d !extras appliedArgs' ->
            exitDerived $
              toDyn $ FullyEffected d extras $! appliedArgs ++ appliedArgs'
          where
            exitDerived :: Dynamic -> Edh EdhValue
            exitDerived dd = do
              !ets <- edhThreadState
              let ctx = edh'context ets
                  scope = contextScope ctx
                  this = edh'scope'this scope
              !newOid <- newUniqueEdh
              return $
                EdhObject
                  this
                    { edh'obj'ident = newOid,
                      edh'obj'store = HostStore dd
                    }

    thisScripted :: Edh ScriptedResult
    thisScripted = do
      !ets <- edhThreadState
      let !this = edh'scope'this $ contextScope $ edh'context ets
      case edh'obj'store this of
        HostStore !dhs -> case fromDynamic dhs of
          Just (sr :: ScriptedResult) -> return sr
          Nothing -> naM "bug: this is not a scripted Comput"
        _ -> naM "bug: Comput not a host object"

appliedArgByKey :: AttrKey -> [(ComputArgDecl, EdhValue)] -> EdhValue
appliedArgByKey k = go
  where
    go [] = nil
    go ((ComputArgDecl _eff !ak _type, val) : rest)
      | ak == k = val
      | otherwise = go rest

-- | Apply a mapper over the effected host value, a new object (with new
-- identity) will be produced, inheriting all aspects of the original object
mapEffectedComput ::
  forall a b.
  (Typeable a, Typeable b) =>
  (a -> b) ->
  Object ->
  Edh Object
mapEffectedComput f inst = case edh'obj'store inst of
  HostStore !dhs -> case fromDynamic dhs of
    Just (sr :: ScriptedResult) -> case sr of
      FullyEffected !d !extras !appliedArgs -> tryDynData d $ \ !d' ->
        toDyn $ FullyEffected d' extras appliedArgs
      ScriptDone' !d ->
        -- todo should use id here?
        tryDynData d $ toDyn . ScriptDone'
      _ -> naAct
    _ -> tryDynData dhs id
  _ -> naAct
  where
    naAct = naM $ "not of expected host type: " <> T.pack (show $ typeRep @a)

    tryDynData :: Dynamic -> (Dynamic -> Dynamic) -> Edh Object
    tryDynData dd wd = case fromDynamic dd of
      Nothing -> naAct
      Just (a :: a) -> do
        !newOid <- newUniqueEdh
        return
          inst
            { edh'obj'ident = newOid,
              edh'obj'store = HostStore $ wd $ toDyn $ f a
            }

-- | Obtain the 'Dynamic' value of a host object, it can be an effected comput
-- or a raw host value
dynamicHostData :: Object -> Maybe Dynamic
dynamicHostData !obj = case edh'obj'store obj of
  HostStore !dhs -> case fromDynamic dhs of
    Just (sr :: ScriptedResult) -> case sr of
      FullyEffected !d _extras _appliedArgs -> Just d
      ScriptDone' !d -> Just d
      _ -> Nothing
    _ -> Just dhs
  _ -> Nothing

hostInstanceOf :: forall t. (Typeable t) => Object -> Edh t
hostInstanceOf !inst = case dynamicHostData inst of
  Nothing ->
    naM $
      "not a host object with expected type: " <> T.pack (show $ typeRep @t)
  Just dd@(Dynamic tr _) -> case fromDynamic dd of
    Nothing ->
      naM $
        "a " <> edhClassName inst
          <> " object wraps a host value of type '"
          <> T.pack (show tr)
          <> "' instead of expected: "
          <> T.pack (show $ typeRep @t)
    Just (d :: t) -> return d

thisHostObjectOf :: forall t. (Typeable t) => Edh t
thisHostObjectOf = do
  !ets <- edhThreadState
  let !this = edh'scope'this $ contextScope $ edh'context ets
  (hostInstanceOf @t this <|>) $
    naM $
      "bug: this object is not wrapping a host value of type: "
        <> T.pack (show $ typeRep @t)

{- HLINT ignore "Redundant <$>" -}

hostObjectOf :: forall t. (Typeable t) => Object -> Edh (Object, t)
hostObjectOf !obj = (obj :) <$> readTVarEdh (edh'obj'supers obj) >>= go
  where
    go :: [Object] -> Edh (Object, t)
    go [] = do
      !badDesc <- edhObjDescM obj
      naM $
        "object " <> badDesc
          <> " does not wrap an expected host value of type: "
          <> T.pack (show $ typeRep @t)
    go (inst : rest) = case dynamicHostData inst of
      Nothing -> go rest
      Just !dd -> case fromDynamic dd of
        Nothing -> go rest
        Just (d :: t) -> return (inst, d)

hostObjectOf' :: forall t. (Typeable t) => EdhValue -> Edh (Object, t)
hostObjectOf' !val = case edhUltimate val of
  EdhObject !obj -> hostObjectOf obj
  _ -> do
    !badDesc <- edhValueDescM val
    naM $
      badDesc <> " is not an expected host object of type: "
        <> T.pack (show $ typeRep @t)
