"""
Event processing constructs at par to Edh's

The channel construct here is similar to STM's broadcast TChan, see:
  http://hackage.haskell.org/package/stm/docs/Control-Concurrent-STM-TChan.html
While no unicast TChan needed here, the design is simplified to PubChan and
SubChan.

For intuition:
    *) PubChan can be thought of as the write-only broadcast TChan.
    *) SubChan can be thought of as the TChan dup'ed from a broadcast TChan,
       which will only ever be read.

Like a broadcast TChan, a PubChan itself is not buffering items, when there is
no SubChan reading its item stream, any item written to the PubChan is
discarded immediately.

Like you can dup multiple TChan from a broadcast TChan, you can create multiple
SubChan from a common PubChan, then have them consuming items from the common
PubChan concurrently.

A SubChan's buffer is unbounded, so here's a caveat that slow consumers with a
faster producer will constantly increase the program's memory footprint, i.e.
items will pile up in memory.

"""
__all__ = ["PubChan", "SubChan", "EventSink"]

import asyncio

from typing import *

from .ctrl import *
from .adt import *


class PubChan:
    """
    Publisher's channel, write only

    The `stream()` method coroutine can be called with async-for from
    a consumer task to consume subsquent items published to this channel.

    """

    __slots__ = "nxt"

    def __init__(self):
        loop = asyncio.get_running_loop()
        self.nxt = loop.create_future()

    def write(self, ev):
        loop = asyncio.get_running_loop()
        nxt = loop.create_future()
        self.nxt.set_result((ev, nxt))
        self.nxt = nxt

    async def stream(self):
        """
        This is the async iterator to consume subsequent items from this
        channel.
        """
        nxt = self.nxt
        while True:
            (ev, nxt) = await asyncio.shield(nxt)
            if ev is EndOfStream:
                break
            yield ev
            ev = None


class SubChan:
    """
    Subscriber's channel, read only.

    CAVEAT:

    As long as a SubChan is created and stay alive, all subsequent items
    written to its upstream PubChan will be buffered for it, until consumed
    with `subChan.read()`. Consuming a SubChan slower than items being produced
    into its PubChan will increase memory footprint.
    
    """

    __slots__ = "nxt"

    def __init__(self, pubChan: "PubChan"):
        """
        Create a subscriber's channel from a publisher's channel
        """
        self.nxt = pubChan.nxt

    async def read(self):
        (ev, self.nxt) = await asyncio.shield(self.nxt)
        return ev


class EventSink:
    """
    EventSink at par to Edh's

    """

    __slots__ = (
        "seqn",
        "mrv",
        "chan",
    )

    def __init__(self):
        # sequence number
        self.seqn = 0
        # most recent event value
        self.mrv = None
        # the publish channel
        self.chan = PubChan()

    def publish(self, ev):
        if self.seqn >= 9223372036854775807:
            # int64 wrap back to 1 on overflow
            self.seqn = 1
        else:
            self.seqn += 1
        self.mrv = ev
        self.chan.write(ev)

    async def one_more(self):
        if self.seqn > 0 and self.mrv is EndOfStream:
            return EndOfStream  # already at eos
        nxt = self.chan.nxt
        ev, _nxt = await asyncio.shield(nxt)
        return ev

    async def stream(self):
        """
        This is the async iterable an event consumer should use to consume
        subsequent events from this sink.

        """
        if self.seqn > 0:
            if self.mrv is EndOfStream:
                return  # already at eos
            yield self.mrv
        nxt = self.chan.nxt
        while True:
            (ev, nxt) = await asyncio.shield(nxt)
            if ev is EndOfStream:
                break
            yield ev
            ev = None

    async def run_producer(self, producer: Coroutine):
        """
        This is the async iterable that should be used to schedule a producer
        coroutine to run, which is going to publish events into this sink,
        but only after the looping consumer has started consuming events from
        this sink, i.e. to ensure no event from the producer coroutine can
        be missed by the calling consumer.
        """
        nxt = self.chan.nxt
        prod_task = asyncio.create_task(producer)
        while True:
            nxt_task = asyncio.shield(nxt)
            await asyncio.wait(
                [nxt_task, prod_task], return_when=asyncio.FIRST_COMPLETED
            )
            if prod_task.done():
                # propagate any error ever occurred in the producer
                await prod_task
                # continue consuming the stream until eos
                while True:
                    (ev, nxt) = await nxt_task
                    if ev is EndOfStream:
                        return
                    yield ev
                    ev = None
                    nxt_task = asyncio.shield(nxt)
            elif nxt_task.done():
                (ev, nxt) = nxt_task.result()
                if ev is EndOfStream:
                    return
                yield ev
                ev = None

