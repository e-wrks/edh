{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Edh.HostEvs where

import Control.Applicative
import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import Data.Unique
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Comput
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.Monad
import Language.Edh.RtTypes
import Type.Reflection
import Prelude

-- | Indicates whether the relevant event sink is at end-of-stream
type EndOfStream = Bool

-- | Atomic Event Queue to foster the propagation of an event hierarchy
--
-- EIO computations can be scheduled into such a queue as either consequences or
-- subsequences of, the realization of a whole event hierarchy, which is rooted
-- from a single root event (published by 'publishEvent'), then to have more
-- events derived (by 'spreadEvent') from it, either directly or indirectly,
-- finally forming a whole hierarchy of events.
data AtomEvq = AtomEvq
  { aeq'conseqs :: !(TVar [EIO ()]),
    aeq'subseqs :: !(TVar [EIO ()])
  }

-- | Schedule an EIO computation as a consequence of the underlying event
-- spreading
--
-- All consequences will be executed after spreading of the event hierarchy
-- succeeds at all, and before any subsequence is executed. So state changes
-- made by consequent computations are guaranteed to be observed by any
-- subsequent computation.
--
-- No consequence will be executed if the spreading phase fails somehow.
--
-- Currently all consequent/subsequent actions are required to be exception
-- free, any noncomplying exception will be thrown at the nearest scripting
-- exception handler, with the overall event propagation done halfway (i.e.
-- data consistency issues prone). Such exceptions may get caught & ignored in
-- the future, for consequences / subsequences ever armed uncancellable.
conseqDo :: EIO () -> AtomEvq -> STM ()
conseqDo !act (AtomEvq !conseqs _) = modifyTVar' conseqs (act :)

-- | Schedule an EIO computation as a subsequence of the underlying event
-- spreading / propagation
--
-- All subsequences will be executed after spreading of the event hierarchy
-- succeeds at all, and all consequences have been executed. So state changes
-- made by consequent computations are guaranteed to be observed by any
-- subsequent computation.
--
-- No subsequence will be executed if the spreading phase fails somehow.
--
-- Currently all consequent/subsequent actions are required to be exception
-- free, any noncomplying exception will be thrown at the nearest scripting
-- exception handler, with the overall event propagation done halfway (i.e.
-- data consistency issues prone). Such exceptions may get caught & ignored in
-- the future, for consequences / subsequences ever armed uncancellable.
subseqDo :: EIO () -> AtomEvq -> STM ()
subseqDo !act (AtomEvq _ !subseqs) = modifyTVar' subseqs (act :)

class EventSource s t where
  -- | Subscribe to the event stream through the specified event source
  --
  -- Any failure in the handler will prevent publishing of the original event at
  -- all, such a failure will be thrown at the publisher of the original event.
  --
  -- The atomic event queue can be used to schedule EIO computations as
  -- subsequences of the original event. All subsequent EIO computations will be
  -- tried regardless of other's failures, so long as the publishing of the
  -- original event succeeded.
  on :: s t -> (t -> AtomEvq -> STM ()) -> STM ()

  -- | Subscribe to the next event through the specified event source
  --
  -- Any failure in the handler will prevent publishing of the original event at
  -- all, such a failure will be thrown at the publisher of the original event.
  --
  -- The atomic event queue can be used to schedule EIO computations as
  -- subsequences of the original event. All subsequent EIO computations will be
  -- tried regardless of other's failures, so long as the publishing of the
  -- original event succeeded.
  once :: s t -> (t -> AtomEvq -> STM ()) -> STM ()

data MappedEvs s a b = (EventSource s a) => MappedEvs (a -> b) (s a)

instance (EventSource s a) => EventSource (MappedEvs s a) b where
  on (MappedEvs f sa) handler = on sa $ \a aeq -> handler (f a) aeq
  once (MappedEvs f sa) handler = once sa $ \a aeq -> handler (f a) aeq

-- | Polymorphic event source value wrapper
data SomeEventSource t = forall s. (EventSource s t) => SomeEventSource (s t)

instance Functor SomeEventSource where
  fmap f (SomeEventSource evs) = SomeEventSource $ MappedEvs f evs

-- | Polymorphic event source argument adapter
data AnyEventSource
  = forall s t. (EventSource s t, Typeable t) => AnyEventSource (s t) Object

instance Eq AnyEventSource where
  AnyEventSource _ xo == AnyEventSource _ yo = xo == yo

instance ComputArgAdapter AnyEventSource where
  adaptEdhArg !v = (<|> badVal) $ case edhUltimate v of
    EdhObject o -> case dynamicHostData o of
      Nothing -> mzero
      Just (Dynamic tr evs) -> case eqTypeRep tr (typeRep @SomeEventSink) of
        Just HRefl -> case evs of
          SomeEventSink evs' ->
            withTypeable tr $ return $ AnyEventSource evs' o
        _ -> case tr of
          App trEvs trE -> case eqTypeRep trEvs (typeRep @SomeEventSource) of
            Just HRefl -> case evs of
              SomeEventSource evs' ->
                withTypeable trE $ return $ AnyEventSource evs' o
            _ -> case eqTypeRep trEvs (typeRep @EventSink) of
              Just HRefl -> withTypeable trE $ return $ AnyEventSource evs o
              _ -> mzero
          _ -> mzero
    _ -> mzero
    where
      badVal = do
        !badDesc <- edhValueDescM v
        throwEdhM UsageError $
          "any EventSource expected but given: " <> badDesc

  adaptedArgValue (AnyEventSource _evs !obj) = EdhObject obj

-- | Polymorphic event sink value wrapper
data SomeEventSink = forall t. Typeable t => SomeEventSink (EventSink t)

instance Eq SomeEventSink where
  SomeEventSink x == SomeEventSink y = isSameEventSink x y

-- | Polymorphic event sink argument adapter
data AnyEventSink = forall t. Typeable t => AnyEventSink (EventSink t) Object

instance Eq AnyEventSink where
  AnyEventSink x _ == AnyEventSink y _ = isSameEventSink x y

instance ComputArgAdapter AnyEventSink where
  adaptEdhArg !v = (<|> badVal) $ case edhUltimate v of
    EdhObject o -> case dynamicHostData o of
      Nothing -> mzero
      Just (Dynamic tr evs) -> case eqTypeRep tr (typeRep @SomeEventSink) of
        Just HRefl -> case evs of
          SomeEventSink evs' -> withTypeable tr $ return $ AnyEventSink evs' o
        _ -> case tr of
          App trEvs trE -> case eqTypeRep trEvs (typeRep @EventSink) of
            Just HRefl -> withTypeable trE $ return $ AnyEventSink evs o
            _ -> mzero
          _ -> mzero
    _ -> mzero
    where
      badVal = do
        !badDesc <- edhValueDescM v
        throwEdhM UsageError $
          "any EventSink expected but given: " <> badDesc

  adaptedArgValue (AnyEventSink _evs !obj) = EdhObject obj

-- | An event sink conveys an event stream, with possibly multiple event
-- producers and / or multiple event consumers (i.e. listeners and handlers
-- subscribed to the event sink via 'listenEvents' and 'handleEvents')
data EventSink t = EventSink
  { -- | Unique identifier of the event sink, fmap won't change this identity
    event'sink'ident :: Unique,
    -- | Derive a consequent event from an upstream event, as part of the
    -- spreading event hierarchy underlying
    --
    -- The atomic event queue should remain the same for event hierarchy
    -- spreading, it is passed around through 'EventListener's, 'EventHandler's,
    -- and @spreadEvent@ here.
    --
    -- A spreaded event will be published atomically with the upstream event
    -- hierarchy, so all events published within the same spreaded hierarchy
    -- are, guaranteed to be seen via 'recentEvent', by any EIO computation
    -- scheduled as consequence or subsequence of the underlying event
    -- hierarchy.
    spreadEvent :: AtomEvq -> t -> STM (),
    -- | Read most recent event pertained by the event sink
    --
    -- An event is updated as the recent one of the sink (stream), before any
    -- subscribed consumer (listener/handler) is triggered.
    recentEvent :: STM (Maybe t),
    -- | Publish a root event, it may be spreaded to a hierarchy of events, and
    -- finally realized with consequences and subsequences
    --
    -- Return whether the event sink is at end-of-stream after the publication,
    -- if it is already at EoS, 'False' will be returned immediately without
    -- publishing attempted.
    --
    -- Note that any failure during the spreading phase will be thrown to here,
    -- with all effects of the event cancelled (as far as STM rollback did it).
    publishEvent :: t -> EIO EndOfStream,
    -- | Subscribe an event listener to the event sink
    listenEvents :: EventListener t -> STM (),
    -- | Check whether the event sink is at end-of-stream
    atEndOfStream :: STM EndOfStream,
    -- | Mark the event sink to be at end-of-strem
    doneEventStream :: STM ()
  }

-- | An event handler reacts to a particular event with an STM computation,
-- returns whether it is still interested in the subsequent events in the same
-- stream
--
-- Further EIO computations can be scheduled into the provided atomic event
-- queue. Any failure in any event handler will prevent the publishing of the
-- current event hierarchy at all, the failure will be thrown to the publisher
-- of the root event.
type EventHandler t = AtomEvq -> t -> STM HandleSubsequentEvents

data HandleSubsequentEvents = KeepHandling | StopHandling

-- | An event listener reacts to a particular event with an STM computation,
-- returns a possible event listener for the next event in the stream
--
-- Further EIO computations can be scheduled into the provided atomic event
-- queue. Any failure in any event listener will prevent the publishing of the
-- current event hierarchy at all, the failure will be thrown to the publisher
-- of the root event.
--
-- When subsequent events should be processed by the same event listener or not
-- at all, it should be more proper to implement an 'EventHandler'.
newtype EventListener t = EventListener
  {on'event :: AtomEvq -> t -> STM (Maybe (EventListener t))}

-- | Subscribe an event handler to the event sink
handleEvents ::
  forall t.
  Typeable t =>
  EventSink t ->
  EventHandler t ->
  STM ()
handleEvents !evs !handler =
  atEndOfStream evs >>= \case
    True -> return ()
    False -> listenEvents evs keepTriggering
  where
    keepTriggering :: EventListener t
    keepTriggering = EventListener $ \aeq !evd ->
      handler aeq evd >>= \case
        KeepHandling -> return (Just keepTriggering)
        StopHandling -> return Nothing

-- | Create a new event sink
newEventSinkEdh :: forall t. Edh (EventSink t)
newEventSinkEdh = inlineSTM newEventSink

-- | Create a new event sink
newEventSinkEIO :: forall t. EIO (EventSink t)
newEventSinkEIO = atomicallyEIO newEventSink

-- | Create a new event sink
newEventSink :: forall t. STM (EventSink t)
newEventSink = do
  !esid <- unsafeIOToSTM newUnique
  !eosRef <- newTVar False
  !rcntRef <- newTVar Nothing
  !subsRef <- newTVar []

  let --
      spreadEvt :: AtomEvq -> t -> STM ()
      spreadEvt = _spread'event eosRef rcntRef subsRef

      recentEvt :: STM (Maybe t)
      recentEvt = readTVar rcntRef

      publishEvt :: t -> EIO EndOfStream
      publishEvt = _publish'event eosRef rcntRef subsRef

      listenEvs :: EventListener t -> STM ()
      listenEvs = _listen'events eosRef subsRef

      atEoS :: STM EndOfStream
      atEoS = readTVar eosRef

      doneEvs :: STM ()
      doneEvs = writeTVar eosRef True

  return $ EventSink esid spreadEvt recentEvt publishEvt listenEvs atEoS doneEvs

isSameEventSink :: forall a b. EventSink a -> EventSink b -> Bool
isSameEventSink a b = event'sink'ident a == event'sink'ident b

-- | Note identity of event sinks won't change after fmap'ped
instance Eq (EventSink a) where
  (==) = isSameEventSink

_spread'event ::
  forall t.
  TVar EndOfStream ->
  TVar (Maybe t) ->
  TVar [EventListener t] ->
  AtomEvq ->
  t ->
  STM ()
_spread'event !eosRef !rcntRef !subsRef !aeq !evd =
  readTVar eosRef >>= \case
    True -> return ()
    False -> do
      writeTVar rcntRef $ Just evd
      readTVar subsRef >>= \case
        -- short-circuit when there are no subscribers
        [] -> return ()
        -- drive subscribers to spread the current event hierarchy
        !subs -> do
          !subs' <- _spread'to'subscribers aeq evd subs
          conseqDo (atomicallyEIO $ writeTVar subsRef subs') aeq

_spread'to'subscribers ::
  forall t.
  AtomEvq ->
  t ->
  [EventListener t] ->
  STM [EventListener t]
_spread'to'subscribers !aeq !evd !subs = spread [] subs
  where
    spread ::
      [EventListener t] ->
      [EventListener t] ->
      STM [EventListener t]
    spread subsRemain [] = return $! reverse subsRemain -- keep original order
    spread subsRemain (listener : rest) =
      on'event listener aeq evd >>= \case
        Nothing -> spread subsRemain rest
        Just listener' -> spread (listener' : subsRemain) rest

_publish'event ::
  forall t.
  TVar EndOfStream ->
  TVar (Maybe t) ->
  TVar [EventListener t] ->
  t ->
  EIO EndOfStream
_publish'event !eosRef !rcntRef !subsRef !evd =
  readTVarEIO eosRef >>= \case
    True -> return True
    False -> do
      writeTVarEIO rcntRef $ Just evd

      readTVarEIO subsRef >>= \case
        -- short-circuit when there are no subscribers
        [] -> return False
        -- drive subscribers to spread an event hierarchy
        !subs -> do
          !conseqs <- newTVarEIO []
          !subseqs <- newTVarEIO []

          atomicallyEIO $
            _spread'to'subscribers (AtomEvq conseqs subseqs) evd subs
              >>= writeTVar subsRef

          -- execute the consequences
          readTVarEIO conseqs >>= propagate

          -- execute the subsequences
          readTVarEIO subseqs >>= propagate

          readTVarEIO eosRef
  where
    propagate :: [EIO ()] -> EIO ()
    propagate [] = return ()
    propagate (act : rest) = do
      act -- TODO should catch any tolerable exception, and keep going in case
      propagate rest

_listen'events ::
  forall t.
  TVar EndOfStream ->
  TVar [EventListener t] ->
  EventListener t ->
  STM ()
_listen'events !eosRef !subsRef !listener =
  readTVar eosRef >>= \case
    True -> return ()
    False -> modifyTVar' subsRef (listener :)

instance (Typeable t) => EventSource EventSink t where
  on !evs !handler = handleEvents evs $ \ !aeq !evd -> do
    handler evd aeq
    return KeepHandling

  once !evs !handler = handleEvents evs $ \ !aeq !evd -> do
    handler evd aeq
    return StopHandling

-- | Spread new event stream(s), as part of the spreading of an upstream event
-- stream
--
-- Any failure in the spreading will prevent publishing of the original event
-- hierarchy at all, such a failure will be thrown at the publisher of the
-- original root event.
--
-- The spreading stops after the 'stopOnEoS' callback indicates so, per any
-- downstream event sink reaches EoS.
spreadEvents ::
  forall t.
  Typeable t =>
  (SomeEventSink -> STM Bool) ->
  EventSink t ->
  ((forall t'. Typeable t' => EventSink t' -> t' -> STM ()) -> t -> STM ()) ->
  STM ()
spreadEvents !stopOnEoS !intake !deriver = do
  !stopVar <- newTVar False
  handleEvents intake $ \ !aeq !evd -> do
    let spreader :: forall t'. Typeable t' => EventSink t' -> t' -> STM ()
        spreader evs' d' =
          atEndOfStream evs' >>= \case
            True ->
              stopOnEoS (SomeEventSink evs') >>= \case
                True -> writeTVar stopVar True
                False ->
                  throwHostSTM UsageError "spreading to an EventSink at eos"
            False -> spreadEvent evs' aeq d'
    readTVar stopVar >>= \case
      True -> return StopHandling
      False -> do
        deriver spreader evd
        readTVar stopVar >>= \case
          True -> return StopHandling
          False -> return KeepHandling

-- | Generate new event stream(s), as the consequence of the specified upstream
-- event stream
--
-- Currently all consequent/subsequent actions are required to be exception
-- free, any noncomplying exception will be thrown at the nearest scripting
-- exception handler, with the overall event propagation done halfway (i.e.
-- data consistency issues prone). Such exceptions may get caught & ignored in
-- the future, for consequences / subsequences ever armed uncancellable.
--
-- The generation stops after the 'stopOnEoS' callback indicates so, per any
-- downstream event sink reaches EoS.
generateEvents ::
  forall t.
  Typeable t =>
  (SomeEventSink -> STM Bool) ->
  EventSink t ->
  ((forall t'. Typeable t' => EventSink t' -> t' -> EIO ()) -> t -> EIO ()) ->
  EIO ()
generateEvents !stopOnEoS !intake !deriver = do
  !stopVar <- newTVarEIO False
  let publisher :: forall t'. Typeable t' => EventSink t' -> t' -> EIO ()
      publisher evs' d' = do
        atomicallyEIO (atEndOfStream evs') >>= markStop
        publishEvent evs' d' >>= markStop
        where
          markStop :: Bool -> EIO ()
          markStop = \case
            False -> pure ()
            True ->
              atomicallyEIO $
                stopOnEoS (SomeEventSink evs') >>= \case
                  True -> writeTVar stopVar True
                  False ->
                    throwHostSTM
                      UsageError
                      "publishing to an EventSink at eos"

  atomicallyEIO $
    handleEvents intake $ \ !aeq !evd ->
      readTVar stopVar >>= \case
        True -> return StopHandling
        False -> do
          conseqDo (deriver publisher evd) aeq
          return KeepHandling

stopWhenAllEventSinksAtEoS ::
  [SomeEventSink] -> STM (SomeEventSink -> STM Bool)
stopWhenAllEventSinksAtEoS evss = do
  !eosVars <- sequence $ (<$> evss) $ \ !evs -> (evs,) <$> newTVar False
  return $ \ !evs -> do
    -- TODO optim. perf.
    let markAndCheck :: Bool -> [(SomeEventSink, TVar Bool)] -> STM Bool
        markAndCheck !nonStop [] = return $ not nonStop
        markAndCheck !nonStop ((chkEvs, eosVar) : rest)
          | chkEvs == evs = do
            writeTVar eosVar True
            markAndCheck nonStop rest
          | otherwise =
            readTVar eosVar >>= \case
              False -> markAndCheck True rest
              True -> markAndCheck nonStop rest
    markAndCheck False eosVars
