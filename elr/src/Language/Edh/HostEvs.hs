{-# LANGUAGE InstanceSigs #-}

module Language.Edh.HostEvs where

import Control.Applicative
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.Dynamic
import Data.IORef
import Data.Unique
import GHC.Conc (unsafeIOToSTM)
import System.IO
import Prelude

-- | Indicates whether the relevant event sink is at end-of-stream
type EndOfStream = Bool

-- | Atomic Event Queue to foster the propagation of an event hierarchy
--
-- IO computations can be scheduled into such a queue as either consequences or
-- subsequences of, the realization of a whole event hierarchy, which is rooted
-- from a single root event (published by 'publishEvent'), then to have more
-- events derived (by 'spreadEvent') from it, either directly or indirectly,
-- finally forming a whole hierarchy of events.
data AtomEvq = AtomEvq
  { aeq'conseqs :: !(TVar [IO ()]),
    aeq'subseqs :: !(TVar [IO ()])
  }

-- | Schedule an IO computation as a consequence of the underlying event
-- spreading
--
-- All consequences will be executed after spreading of the event hierarchy
-- succeeds at all, and before any subsequence is executed. So state changes
-- made by consequent computations are guaranteed to be observed by any
-- subsequent computation.
--
-- No consequence will be executed if the spreading phase fails somehow.
--
-- Especially note that any failure during any consequence is ignored.
conseqIO :: AtomEvq -> IO () -> STM ()
conseqIO (AtomEvq !conseqs _) !act = modifyTVar' conseqs (act :)

-- | Schedule an IO computation as a subsequence of the underlying event
-- spreading / propagation
--
-- All subsequences will be executed after spreading of the event hierarchy
-- succeeds at all, and all consequences have been executed. So state changes
-- made by consequent computations are guaranteed to be observed by any
-- subsequent computation.
--
-- No subsequence will be executed if the spreading phase fails somehow.
--
-- Especially note that any failure during any consequence or subsequence is
-- ignored.
subseqIO :: AtomEvq -> IO () -> STM ()
subseqIO (AtomEvq _ !subseqs) !act = modifyTVar' subseqs (act :)

-- | An event handler reacts to a particular event with an STM computation,
-- returns whether it is still interested in the subsequent events in the same
-- stream
--
-- Further IO computations can be scheduled into the provided atomic event
-- queue. Any failure in any event handler will prevent the publishing of the
-- current event hierarchy at all, the failure will be thrown to the publisher
-- of the root event.
type EventHandler t = AtomEvq -> t -> STM HandleSubsequentEvents

data HandleSubsequentEvents = KeepHandling | StopHandling

-- | An event listener reacts to a particular event with an STM computation,
-- returns a possible event listener for the next event in the stream
--
-- Further IO computations can be scheduled into the provided atomic event
-- queue. Any failure in any event listener will prevent the publishing of the
-- current event hierarchy at all, the failure will be thrown to the publisher
-- of the root event.
--
-- When subsequent events should be processed by the same event listener or not
-- at all, it should be more proper to implement an 'EventHandler'.
newtype EventListener t = EventListener
  { on'event :: AtomEvq -> t -> STM (Maybe (EventListener t))
  }

-- | The polymorphic event sink wrapper
data SomeEventSink = forall t. Typeable t => SomeEventSink (EventSink t)

instance Eq SomeEventSink where
  SomeEventSink x == SomeEventSink y = isSameEventSink x y

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
    -- spreading, is is passed around through 'EventListener's, 'EventHandler's,
    -- and @spreadEvent@ here.
    --
    -- A spreaded event will be published atomically with the upstream event
    -- hierarchy, so all events published within the same spreaded hierarchy
    -- are, guaranteed to be seen via 'recentEvent', by any IO computation
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
    publishEvent :: t -> IO EndOfStream,
    -- | Subscribe an event listener to the event sink
    listenEvents :: EventListener t -> IO (),
    -- | Check whether the event sink is at end-of-stream
    atEndOfStream :: STM EndOfStream,
    -- | Mark the event sink to be at end-of-strem
    doneEventStream :: STM ()
  }

-- | Subscribe an event handler to the event sink
handleEvents ::
  forall t.
  Typeable t =>
  EventSink t ->
  EventHandler t ->
  IO ()
handleEvents !evs !handler =
  atomically (atEndOfStream evs) >>= \case
    True -> return ()
    False -> listenEvents evs keepTriggering
  where
    keepTriggering :: EventListener t
    keepTriggering = EventListener $
      \aeq !evd ->
        handler aeq evd >>= \case
          KeepHandling -> return (Just keepTriggering)
          StopHandling -> return Nothing

-- | Create a new event sink
newEventSink :: forall t. IO (EventSink t)
newEventSink = do
  !esid <- newUnique
  !eosRef <- newTVarIO False
  !rcntRef <- newTVarIO Nothing
  !subsRef <- newIORef []

  let --
      spreadEvt :: AtomEvq -> t -> STM ()
      spreadEvt = _spread'event atEoS rcntRef subsRef

      recentEvt :: STM (Maybe t)
      recentEvt = readTVar rcntRef

      publishEvt :: t -> IO EndOfStream
      publishEvt = _publish'event eosRef rcntRef subsRef

      listenEvs :: EventListener t -> IO ()
      listenEvs = _listen'events atEoS subsRef

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

-- | Note that this 'Functor' instance is lawless w.r.t. event
-- spreading/publishing, i.e. 'spreadEvent' and 'publishEvent' are prohibited
-- against a decorated event sink, even 'fmap'ped with `id`.
--
-- Though it is lawful otherwise, i.e. w.r.t. event consuming and EoS semantics.
instance Functor EventSink where
  fmap :: forall a b. (a -> b) -> EventSink a -> EventSink b
  fmap
    f
    ( EventSink
        !esid
        _spreadEvt
        recentEvt
        _publishEvt
        listenEvs
        atEoS
        doneEvs
      ) =
      do
        let spreadEvt' :: AtomEvq -> b -> STM ()
            spreadEvt' _ _ =
              throwSTM $
                userError
                  "prohibited against a decorated event sink"

            recentEvt' :: STM (Maybe b)
            recentEvt' = fmap f <$> recentEvt

            publishEvt' :: b -> IO EndOfStream
            publishEvt' _ =
              throwIO $
                userError
                  "prohibited against a decorated event sink"

            listenEvs' :: EventListener b -> IO ()
            listenEvs' !listener = listenEvs $ deleListener listener
              where
                deleListener :: EventListener b -> EventListener a
                deleListener (EventListener listener') =
                  EventListener $ \aeq evd ->
                    listener' aeq (f evd) >>= \case
                      Nothing -> return Nothing
                      Just !nextListener ->
                        return $ Just $ deleListener nextListener

        EventSink
          esid
          spreadEvt'
          recentEvt'
          publishEvt'
          listenEvs'
          atEoS
          doneEvs

_spread'event ::
  forall t.
  STM EndOfStream ->
  TVar (Maybe t) ->
  IORef [EventListener t] ->
  AtomEvq ->
  t ->
  STM ()
_spread'event !eos !rcntRef !subsRef !aeq !evd =
  eos >>= \case
    True -> return ()
    False -> do
      writeTVar rcntRef $ Just evd
      unsafeIOToSTM (readIORef subsRef) >>= \case
        -- short-circuit when there are no subscribers
        [] -> return ()
        -- drive subscribers to spread the current event hierarchy
        !subs -> do
          !subs' <- _spread'to'subscribers aeq evd subs
          conseqIO aeq $ writeIORef subsRef subs'

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
  IORef [EventListener t] ->
  t ->
  IO EndOfStream
_publish'event !eosRef !rcntRef !subsRef !evd =
  readTVarIO eosRef >>= \case
    True -> return True
    False ->
      readIORef subsRef >>= \case
        -- short-circuit when there are no subscribers
        [] -> do
          atomically $ writeTVar rcntRef $ Just evd
          return False
        -- drive subscribers to spread an event hierarchy
        !subs -> do
          !conseqs <- newTVarIO []
          !subseqs <- newTVarIO []

          (writeIORef subsRef =<<) $
            atomically $ do
              writeTVar rcntRef $ Just evd
              _spread'to'subscribers (AtomEvq conseqs subseqs) evd subs

          -- execute the consequences
          readTVarIO conseqs >>= propagate

          -- execute the subsequences
          readTVarIO subseqs >>= propagate

          -- now let's check if it has lost all its subscribers after even
          -- subsequences realized, and if that's the case, mark it EoS
          readTVarIO eosRef >>= \case
            True -> return True
            False ->
              readIORef subsRef >>= \case
                [] -> do
                  atomically $ writeTVar eosRef True
                  return True
                _ -> return False
  where
    propagate :: [IO ()] -> IO ()
    propagate [] = return ()
    propagate (act : rest) = do
      catch act $ \(SomeException exc) ->
        hPutStrLn stderr $
          "Unexpected exception in event propagation: " <> show exc
      propagate rest

_listen'events ::
  forall t.
  STM EndOfStream ->
  IORef [EventListener t] ->
  EventListener t ->
  IO ()
_listen'events !eos !subsRef !listener =
  atomically eos >>= \case
    True -> return ()
    False -> modifyIORef' subsRef (listener :)

-- | Subscribe to the event stream through the specified event sink
--
-- Any failure in the handler will prevent publishing of the original event at
-- all, such a failure will be thrown at the publisher of the original event.
--
-- The atomic event queue can be used to schedule IO computations as
-- subsequences of the original event. All subsequent IO computations will be
-- tried regardless of other's failures, so long as the publishing of the
-- original event succeeded.
on :: forall t. Typeable t => EventSink t -> (AtomEvq -> t -> STM ()) -> IO ()
on !evs !handler = handleEvents evs $ \ !aeq !evd -> do
  handler aeq evd
  return KeepHandling

-- | Subscribe to the next event through the specified event sink
--
-- Any failure in the handler will prevent publishing of the original event at
-- all, such a failure will be thrown at the publisher of the original event.
--
-- The atomic event queue can be used to schedule IO computations as
-- subsequences of the original event. All subsequent IO computations will be
-- tried regardless of other's failures, so long as the publishing of the
-- original event succeeded.
once :: forall t. Typeable t => EventSink t -> (AtomEvq -> t -> STM ()) -> IO ()
once !evs !handler = handleEvents evs $ \ !aeq !evd -> do
  handler aeq evd
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
  IO ()
spreadEvents !stopOnEoS !intake !deriver = do
  !stopVar <- newTVarIO False
  handleEvents intake $ \ !aeq !evd -> do
    let spreader :: forall t'. Typeable t' => EventSink t' -> t' -> STM ()
        spreader evs' d' =
          atEndOfStream evs' >>= \case
            True ->
              stopOnEoS (SomeEventSink evs') >>= \case
                True -> writeTVar stopVar True
                False -> spreadEvent evs' aeq d'
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
-- Failures in the generation won't prevent publishing of the original event,
-- other consequences / subsequences of the original event hierarchy will
-- propagate anyway.
--
-- The generation stops after the 'stopOnEoS' callback indicates so, per any
-- downstream event sink reaches EoS.
generateEvents ::
  forall t.
  Typeable t =>
  (SomeEventSink -> IO Bool) ->
  EventSink t ->
  ((forall t'. Typeable t' => EventSink t' -> t' -> IO ()) -> t -> IO ()) ->
  IO ()
generateEvents !stopOnEoS !intake !deriver = do
  !stopVar <- newTVarIO False
  let publisher :: forall t'. Typeable t' => EventSink t' -> t' -> IO ()
      publisher evs' d' = do
        atomically (atEndOfStream evs') >>= markStop
        publishEvent evs' d' >>= markStop
        where
          markStop = \case
            True ->
              stopOnEoS (SomeEventSink evs') >>= \case
                True -> atomically $ writeTVar stopVar True
                False -> pure ()
            False -> pure ()

  handleEvents intake $ \ !aeq !evd ->
    readTVar stopVar >>= \case
      True -> return StopHandling
      False -> do
        conseqIO aeq $ deriver publisher evd
        return KeepHandling

stopWhenAllEventSinksAtEoS :: [SomeEventSink] -> IO (SomeEventSink -> IO Bool)
stopWhenAllEventSinksAtEoS evss = do
  !eosVars <- sequence $ (<$> evss) $ \ !evs -> (evs,) <$> newIORef False
  return $ \ !evs -> do
    -- TODO optim. perf.
    let markAndCheck :: Bool -> [(SomeEventSink, IORef Bool)] -> IO Bool
        markAndCheck !nonStop [] = return $ not nonStop
        markAndCheck !nonStop ((chkEvs, eosVar) : rest)
          | chkEvs == evs = do
            writeIORef eosVar True
            markAndCheck nonStop rest
          | otherwise =
            readIORef eosVar >>= \case
              False -> markAndCheck True rest
              True -> markAndCheck nonStop rest
    markAndCheck False eosVars
