{-# LANGUAGE InstanceSigs #-}

module Language.Edh.HostEvs where

import Control.Applicative
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.Dynamic
import Data.Unique
import Language.Edh.Control
import Language.Edh.Evaluate
import Language.Edh.RtTypes
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
    aeq'subseqs :: !(TVar [IO ()]),
    aeq'conts :: !(TVar [Edh ()])
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
conseqIO (AtomEvq !conseqs _ _) !act = modifyTVar' conseqs (act :)

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
subseqIO (AtomEvq _ !subseqs _) !act = modifyTVar' subseqs (act :)

-- | Schedule an Edh computation (which is continuation per se) to be triggered,
-- after all consequences and subsequences of an event has been realized.
--
-- Note: Only in such computations Edh scripting artifacts can be called in a
-- monadic way, with 'IO' or 'STM' monad, that's possible only in CPS and if
-- you have an 'EdhThreadState' available
--
-- Note: Scripting computations are generally much slower than 'IO' or 'STM'
-- computations.
contsEdh :: AtomEvq -> Edh () -> STM ()
contsEdh (AtomEvq _ _ !conts) !act = modifyTVar' conts (act :)

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
    -- spreading, it is passed around through 'EventListener's, 'EventHandler's,
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
    publishEvent :: t -> Edh EndOfStream,
    -- | Subscribe an event listener to the event sink
    listenEvents :: EventListener t -> STM (),
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
  STM ()
handleEvents !evs !handler =
  atEndOfStream evs >>= \case
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
  !subsRef <- newTVarIO []

  let --
      spreadEvt :: AtomEvq -> t -> STM ()
      spreadEvt = _spread'event eosRef rcntRef subsRef

      recentEvt :: STM (Maybe t)
      recentEvt = readTVar rcntRef

      publishEvt :: t -> Edh EndOfStream
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

            publishEvt' :: b -> Edh EndOfStream
            publishEvt' _ =
              throwEdhM
                UsageError
                "prohibited against a decorated event sink"

            listenEvs' :: EventListener b -> STM ()
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
          conseqIO aeq $ atomically $ writeTVar subsRef subs'

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
  Edh EndOfStream
_publish'event !eosRef !rcntRef !subsRef !evd = Edh $ \ !exit !ets ->
  runEdhTx ets $
    edhContIO $
      readTVarIO eosRef >>= \case
        True -> atomically $ exitEdh ets exit True
        False ->
          readTVarIO subsRef >>= \case
            -- short-circuit when there are no subscribers
            [] -> atomically $ do
              writeTVar rcntRef $ Just evd
              exitEdh ets exit False
            -- drive subscribers to spread an event hierarchy
            !subs -> do
              !conseqs <- newTVarIO []
              !subseqs <- newTVarIO []
              !conts <- newTVarIO []

              (atomically . writeTVar subsRef =<<) $
                atomically $ do
                  writeTVar rcntRef $ Just evd
                  _spread'to'subscribers
                    (AtomEvq conseqs subseqs conts)
                    evd
                    subs

              -- execute the consequences
              readTVarIO conseqs >>= propagate

              -- execute the subsequences
              readTVarIO subseqs >>= propagate

              -- trigger continuation actions
              !cas <- readTVarIO conts
              atomically $
                runEdhTx ets $
                  unEdh (sequence_ cas) $ \() _ets ->
                    readTVar eosRef >>= exitEdh ets exit
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
  TVar EndOfStream ->
  TVar [EventListener t] ->
  EventListener t ->
  STM ()
_listen'events !eosRef !subsRef !listener =
  readTVar eosRef >>= \case
    True -> return ()
    False -> modifyTVar' subsRef (listener :)

-- | Subscribe to the event stream through the specified event sink
--
-- Any failure in the handler will prevent publishing of the original event at
-- all, such a failure will be thrown at the publisher of the original event.
--
-- The atomic event queue can be used to schedule IO computations as
-- subsequences of the original event. All subsequent IO computations will be
-- tried regardless of other's failures, so long as the publishing of the
-- original event succeeded.
on ::
  forall t. Typeable t => EventSink t -> (AtomEvq -> t -> STM ()) -> STM ()
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
once ::
  forall t. Typeable t => EventSink t -> (AtomEvq -> t -> STM ()) -> STM ()
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
-- Failures in the generation won't prevent publishing of the original event,
-- other consequences / subsequences of the original event hierarchy will
-- propagate anyway.
--
-- The generation stops after the 'stopOnEoS' callback indicates so, per any
-- downstream event sink reaches EoS.
generateEvents ::
  forall t.
  Typeable t =>
  (SomeEventSink -> STM Bool) ->
  EventSink t ->
  ((forall t'. Typeable t' => EventSink t' -> t' -> Edh ()) -> t -> IO ()) ->
  Edh ()
generateEvents !stopOnEoS !intake !deriver = Edh $ \ !exit !ets ->
  runEdhTx ets $
    edhContIO $ do
      !stopVar <- newTVarIO False
      let publisher :: forall t'. Typeable t' => EventSink t' -> t' -> Edh ()
          publisher evs' d' = do
            edhInlineSTM (atEndOfStream evs') >>= markStop
            publishEvent evs' d' >>= markStop
            where
              markStop :: Bool -> Edh ()
              markStop = \case
                True ->
                  edhInlineSTM $
                    stopOnEoS (SomeEventSink evs') >>= \case
                      True -> writeTVar stopVar True
                      False ->
                        throwHostSTM
                          UsageError
                          "publishing to an EventSink at eos"
                False -> pure ()

      atomically $ do
        handleEvents intake $ \ !aeq !evd ->
          readTVar stopVar >>= \case
            True -> return StopHandling
            False -> do
              conseqIO aeq $ deriver publisher evd
              return KeepHandling
        exitEdh ets exit ()

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
