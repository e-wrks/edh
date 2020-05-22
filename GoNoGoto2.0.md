# Let's `go`, but not that `goto` `2.0`

(this is a write up WIP, major updates planned)

I totally agree with the blame on various concurrency initiating primitives
in most programming languages/runtimes of today, as pointed out in
[Notes on structured concurrency, or: Go statement considered harmful](https://vorpus.org/blog/notes-on-structured-concurrency-or-go-statement-considered-harmful)
, but I see faith from **algebraic effects**, which bears even greater
ambitions with elegance, to have various programming language constructs,
concurrency included, finally implemented a top a single system, as
individual effects.

I argue that, there can exist a version of `go` statement, not guilty on
the **`goto` 2.0** charge, here's my advocacy.

## The design

As `go` does spawn/fork a new execution thread for sure, we can have
some complementary machinery to improve the situation.

### `defer` - the important friend

**Go** provides `defer` for cleanup at end-of-life of a function, here
I suggest to provide a version of `defer` for cleanup at end-of-life of
a thread.

### far-reaching of exception handlers

Traditional wisdom for exception handling always set independance for
forkee threads by default, explicitly propagation of exceptions from
forkee to forker is necessary.

We can change that by putting forkee's call stack on top of forker's
stack, so an exception occurred in the forkee would propagate to
forker's handlers by default.

This means multi-shot of an exception handler on a frame of the
forker's stack, may have its own quirks, yet to be explored.

### main thread should manage lifetime

Regarding cancellation, we can take OS's process group concept, to
identify some forker thread as thread group leader, or call it main
thread if not too confusing. Then upon termination of a main thread,
all its forkee threads are terminated, by ceasing each's chunk
execution, and execute all `defer`ed computations scheduled on it,
then discard it.
