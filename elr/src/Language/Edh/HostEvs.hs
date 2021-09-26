{-# LANGUAGE MultiParamTypeClasses #-}

module Language.Edh.HostEvs where

import Control.Applicative
import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import Data.Unique
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Comput
import Language.Edh.Monad
import Language.Edh.RtTypes
import Type.Reflection
import Prelude

-- * Generic Event Source & Event Handling

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

class EventSource s t where
  -- | Obtain the lingering event data if any
  --
  -- Some event source can always have the latest event data lingering, some
  -- never, some per specific criteria.
  lingering :: s t -> STM (Maybe t)

  -- | Handle each event data as it arrives
  perceive :: s t -> EventHandler t -> STM ()

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
  on !evs !handler = perceive evs $ \ !aeq !evd -> do
    handler evd aeq
    return KeepHandling

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
  once !evs !handler = perceive evs $ \ !aeq !evd -> do
    handler evd aeq
    return StopHandling

perceiveM :: (EventSource s t) => s t -> EventHandler t -> Edh ()
perceiveM evs handler = inlineSTM $ perceive evs handler

onM :: (EventSource s t) => s t -> (t -> AtomEvq -> STM ()) -> Edh ()
onM evs handler = inlineSTM $ on evs handler

onceM :: (EventSource s t) => s t -> (t -> AtomEvq -> STM ()) -> Edh ()
onceM evs handler = inlineSTM $ on evs handler

-- ** SomeEventSource the Functor

data MappedEvs s a b = (EventSource s a) => MappedEvs (a -> b) (s a)

instance (EventSource s a) => EventSource (MappedEvs s a) b where
  lingering (MappedEvs f sa) = fmap f <$> lingering sa
  perceive (MappedEvs f sa) handler = perceive sa $ \aeq a -> handler aeq (f a)

-- | Polymorphic event source value wrapper
data SomeEventSource t = forall s. (EventSource s t) => SomeEventSource (s t)

instance Functor SomeEventSource where
  fmap f (SomeEventSource evs) = SomeEventSource $ MappedEvs f evs

-- ** AnyEventSource the Argument Adapter

-- | Polymorphic event source argument adapter
data AnyEventSource
  = forall s t. (EventSource s t, Typeable t) => AnyEventSource (s t) Object

instance Eq AnyEventSource where
  AnyEventSource _ xo == AnyEventSource _ yo = xo == yo

instance ComputArgAdapter AnyEventSource where
  adaptEdhArg !v = case edhUltimate v of
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

  adaptedArgValue (AnyEventSource _evs !obj) = EdhObject obj

-- * Event Sink - Event Target as well as Event Source

-- | An event sink conveys an event stream, with possibly multiple event
-- producers and / or multiple event consumers (i.e. listeners and handlers
-- subscribed to the event sink via 'listenEvents' and 'handleEvents')
data EventSink t = EventSink
  { -- | Unique identifier of the event sink, fmap won't change this identity
    event'sink'ident :: Unique,
    -- | Subscribed event listeners to this sink
    event'sink'subscribers :: TVar [EventListener t],
    -- | The most recent event data lingering in this sink
    event'sink'recent :: TVar (Maybe t),
    -- | State of end-of-stream
    event'sink'eos :: TVar EndOfStream
  }

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
  readTVar eosRef >>= \case
    True -> return ()
    False -> modifyTVar' subsRef (keepTriggering :)
  where
    eosRef = event'sink'eos evs
    subsRef = event'sink'subscribers evs

    keepTriggering :: EventListener t
    keepTriggering = EventListener $ \aeq !evd ->
      handler aeq evd >>= \case
        KeepHandling -> return (Just keepTriggering)
        StopHandling -> return Nothing

-- ** SomeEventSink the Polymorphic Wrapper

-- | Polymorphic event sink value wrapper
data SomeEventSink = forall t. Typeable t => SomeEventSink (EventSink t)

instance Eq SomeEventSink where
  SomeEventSink x == SomeEventSink y = isSameEventSink x y

-- ** AnyEventSink the Argument Adapter

-- | Polymorphic event sink argument adapter
data AnyEventSink = forall t. Typeable t => AnyEventSink (EventSink t) Object

instance Eq AnyEventSink where
  AnyEventSink x _ == AnyEventSink y _ = isSameEventSink x y

instance ComputArgAdapter AnyEventSink where
  adaptEdhArg !v = case edhUltimate v of
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

  adaptedArgValue (AnyEventSink _evs !obj) = EdhObject obj

-- ** Utilities & Implementation Details

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
  return $ EventSink esid subsRef rcntRef eosRef

isSameEventSink :: forall a b. EventSink a -> EventSink b -> Bool
isSameEventSink a b = event'sink'ident a == event'sink'ident b

-- | Note identity of event sinks won't change after fmap'ped
instance Eq (EventSink a) where
  (==) = isSameEventSink

instance (Typeable t) => EventSource EventSink t where
  lingering = readTVar . event'sink'recent
  perceive = handleEvents

-- * Event Propagation

-- | Run a publisher action, with given event queue and frame driver
--
-- The frame driver is used to realize all effects by consequences/subsequences
-- of all events spreaded before its run, i.e. to drive an event frame
publishEvents :: forall r. (AtomEvq -> EIO () -> EIO r) -> EIO r
publishEvents !publisher = do
  !conseqs <- newTVarEIO []
  !subseqs <- newTVarEIO []
  let aeq = AtomEvq conseqs subseqs

      frameDriver :: EIO ()
      frameDriver = do
        -- realize all consequences
        drain conseqs
        -- realize all subsequences
        drain subseqs
        where
          drain :: TVar [EIO ()] -> EIO ()
          drain q =
            readTVarEIO q >>= \case
              [] -> return ()
              acts -> do
                writeTVarEIO q []
                propagate acts
                drain q
          propagate :: [EIO ()] -> EIO ()
          propagate [] = return ()
          propagate (act : rest) = do
            act -- TODO catch any tolerable exception, and keep going
            propagate rest

  publisher aeq frameDriver

-- | Spread one event data into the specified sink, as within current event
-- frame
--
-- Consequent actions will see all event sinks updated with recent event data
-- in the frame. While subsequent actions will see all effects applied by
-- consequent actions in the frame.
spreadEvent :: forall t. Typeable t => AtomEvq -> EventSink t -> t -> STM ()
spreadEvent !aeq !evs !evd =
  readTVar eosRef >>= \case
    True -> return ()
    False -> do
      writeTVar rcntRef $ Just evd
      readTVar subsRef >>= spread [] >>= writeTVar subsRef
  where
    eosRef = event'sink'eos evs
    rcntRef = event'sink'recent evs
    subsRef = event'sink'subscribers evs

    spread ::
      [EventListener t] ->
      [EventListener t] ->
      STM [EventListener t]
    spread subsRemain [] =
      return $! reverse subsRemain -- keep original order
    spread subsRemain (listener : rest) =
      on'event listener aeq evd >>= \case
        Nothing -> spread subsRemain rest
        Just listener' -> spread (listener' : subsRemain) rest

-- | Shorthand of 'spreadEvent' in 'EIO' monad
spreadEventEIO :: forall t. Typeable t => AtomEvq -> EventSink t -> t -> EIO ()
spreadEventEIO !aeq !evs !evd = atomicallyEIO $ spreadEvent aeq evs evd
