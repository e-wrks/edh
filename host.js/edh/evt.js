/**

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

*/

/**

  Publisher's channel, write only

  The `stream()` method coroutine can be called with for await...of from
  a consumer task to consume subsquent items published to this channel.

 */
export class PubChan {
  constructor() {
    const nxt = [null, null, null];
    nxt[0] = new Promise((resolve, reject) => {
      nxt[1] = resolve;
      nxt[2] = reject;
    });
    this.nxt = nxt;
  }

  write(ev) {
    const nxt = [null, null, null];
    nxt[0] = new Promise((resolve, reject) => {
      nxt[1] = resolve;
      nxt[2] = reject;
    });
    const [_prev, resolve, _reject] = this.nxt;
    resolve([ev, nxt]);
    this.nxt = nxt;
  }

  async *stream() {
    var nxt = this.nxt;
    while (true) {
      const [curr, _resolve, _reject] = nxt;
      var [ev, nxt] = await curr;
      if (null === ev) {
        return; // reached end-of-stream
      } else {
        yield ev;
        ev = null;
      }
    }
  }
}

/**

  Subscriber's channel, read only.

  CAVEAT:

  As long as a SubChan is created and stay alive, all subsequent items
  written to its upstream PubChan will be buffered for it, until consumed
  with `subChan.read()`. Consuming a SubChan slower than items being produced
  into its PubChan will increase memory footprint.

 */
export class SubChan {
  /**
    Create a subscriber's channel from a publisher's channel
   */
  constructor(pubChan) {
    this.nxt = pubChan.nxt;
  }
  async read() {
    let [ev, nxt] = await this.nxt;
    this.nxt = nxt;
    return ev;
  }
}

/**
  EventSink at par to Edh's
 */
export class EventSink {
  constructor() {
    this.seqn = 0;
    this.mrv = null;
    this.chan = PubChan();
  }

  publish(ev) {
    if (this.seqn >= Number.MAX_SAFE_INTEGER) {
      // 53-bit integer part of float64 wrap back to 1 on overflow
      this.seqn = 1;
    } else {
      ++this.seqn;
    }
    this.mrv = ev;
    this.chan.write(ev);
  }

  async oneMore() {
    if (this.seqn > 0 && null === this.mrv) {
      return null; // already at eos
    }
    const nxt = this.chan.nxt;
    const [ev, _nxt] = await nxt;
    return ev;
  }

  /**
    This is the async iterable an event consumer should use to consume
    subsequent events from this sink.
  */
  async *stream() {
    if (this.seqn > 0 && null === this.mrv) {
      return; // already at eos
    }
    yield this.mrv;
    var nxt = this.chan.nxt;
    while (true) {
      const [curr, _resolve, _reject] = nxt;
      var [ev, nxt] = await curr;
      if (null === ev) {
        return; // reached end-of-stream
      } else {
        yield ev;
        ev = null;
      }
    }
  }

  /**
    This is the async iterable that should be used to schedule a producer
    coroutine to run, which is going to publish events into this sink,
    but only after the looping consumer has started consuming events from
    this sink, i.e. to ensure no event from the producer coroutine can
    be missed by the calling consumer.
   */
  async *runProducer(producer) {
    var nxt = this.chan.nxt;
    const producerDone = producer().then((_) => null);
    while (true) {
      let [curr, _resolve, _reject] = nxt;
      // rejection in producer will be propagated out of here immediately
      const result = await Promise.race([producerDone, curr]);
      if (null === result) {
        // producer done without exception
        // continue consuming the stream until eos
        while (true) {
          var [ev, nxt] = await curr;
          if (null === ev) {
            return; // reached end-of-stream
          } else {
            yield ev;
            ev = null;
          }
          let [curr, _resolve, _reject] = nxt;
        }
      } else {
        // producer still running, next event produced
        var [ev, nxt] = result;
        if (null === ev) {
          return; // reached end-of-stream
        } else {
          yield ev;
          ev = null;
        }
      }
    }
  }
}
