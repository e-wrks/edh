# Revision history for Đ (Edh)

## 0.3.0.0

### C3 Linearized Compositional Class

Pre _0.3_, there is only the class procedure, but no class object, version
_0.3_ introduced the class object (whose class is meta class object).

The object system of **Edh** is now a comprehension of previously distinct,
incompatible **OO** constructs. It is both class based and prototype based,
while with composition as the machinery of inheritance, and after all, it's
natively multiple inheritance.

**Edh** class is similar to **Python** class in how multiple inheritance
is supported with
[C3 linearized](https://en.wikipedia.org/wiki/C3_linearization)
**mro** list, but unlike **Python**, each super class in the **mro** list
of an **Edh** class will instantiate a separate object instance, on
construction from an end **Edh** class. Each object instance bears
with a super object list corresponding to its class' **mro** list, and
individual constituent objects can be obtained from an end object by
pattern-matching against the desired super class, this is somehow similar  
to dynamic upcasting to base class in **C++**.

Remained the same as pre _0.3_, inheritance can still happen at the instance
level, i.e. after constructed, an **Edh** object keeps open to `extends`
more super objects, by equivalent host API or eval an `extends` statement
from within any reguar method, either class defined or instance defined,
including `__init__()` .

### Dynamic Scoped Effects

Keyword `effect` is introduced for effectful artifact registration, and
`perform` / `behave` introduced for the resolution.

**Dynamic Scoped Effects** essentially is **Dynamic Scoping** with a separate
effect registration & resolution space, avoided the failure of traditional
**Dynamic Scoping** that lexical artifacts get mixed with callstack provided
artifacts, which further has things confusingly messed up.

### Exception Handling wrt Structured Concurrency

_0.3_ comes with a working exception handling mechanism, similar to that
in **JavaScript** and **Python**.

Additionally in tackling structured concurrency as well as addressing the
needs for dynamic effect resolution, forked threads (go routines) will
invoke its forker's exception handler enclosing the spawn point, for
exceptions not handled by inner _catch_ blocks.

While _finally_ blocks will never be triggered by forked threads.

Especially note that in **Edh**, call frames keep stacking up for a
forked thread atop its forker's call stack, unlike traditional mechanisms
in most other languages/runtimes adhere to POSIX fork semantics. **Edh**
made this design choice so as to allow forkee threads to resolve dynamic
scoped effects against the call stack, even crossing thread boundaries.

And the **hosting pattern** can be used to escape call stack inheritance,
which is technically to have a desirable forker thread loop against a stream
of callable procedures, and make the call in a forked thread for each one
received.

### Preemptive Event Perceiver

The `reactor` procedure before _0.3_ is dropped, `perceive` keyword is
introduced since _0.3_ to install a pattern-matching expression (either a
block or single branch) against each event value received from an event sink.

Event perceivers preempt the execution of the trunk sequence of transactions
on the thread.

Remained the same as pre _0.3_, if a perceiver expression evaluates to
`{break}` value, its **GHC** thread will be terminated, with all scheduled
**defer** actions doing cleanups.

Note that an event perceiver (expression) runs on separate **Edh** thread
(i.e. to say, with its own perceiver/defer list) though on the same **GHC**
thread, so nested perceivers installed for a perceiver thread will cease
effecting after the perceiver expression is fully evaluated.

This makes the guarantee that perceivers installed on a same thread won't
preempt eachothers, and also means that a fired perceiver can block the rest
perceivers (as well as the trunk code of the thread) from running, so it's
unpractical to have long running perceivers, thus even more unpractical to
install & use nested perceivers during a perceiver's execution.

Also a perceiver can `defer` actions to run immediately after its full
synchronous evaluation, upon termination of its own **Edh** thread.

# WIP here

- exception throwing and handling work now, but using operators instead of
  keyword based syntax
  - `throw` statement /w syntax unchanged
  - add `rethrow` statement
  - use (`$=>`) as `catch` and (`@=>`) as `finally`
  - originally planned `try`/`catch`/`finally` keywords and syntax dropped
  - exception classes refactored for Edh code to easily handle host errors
  - far-reaching exception handler
    - forker thread handles exceptions occurred in forkee threads
- reactor procedure dropped, changed to `perceive` construct, same feature
  but different syntax that breaks old code
- the `runtime` module and its host artifacts from default batteries are
  refactored to be `console` module with an implementation in default
  batteries
- Python compatible syntax:
  - (+) can do string concatenation when left-hand is a string
  - triple quoted strings (backtick as well as single/double quotes)
- explicit exports, any artifact must be explicitly defined within an
  export statement to be eligible for import. then neither name nor type
  matters for exportability
- a dynamic effects system
  - define effects with `effect` keyword, pull effectful artifacts with
    `perform` and `behave` keywords
- add `Vector` and `MVector` to default batteries
- `case-of` context match target value now is effective in nested code
  blocks (breaking old code), and `fallthrough` can fall through multiple
  block boundaries only if it's the last statement of those blocks
- to better support functional paradigm and higher order functions,
  procedure declaration statements are turned into expressions, added function
  application operator (\$) and the flipped version (|), which is similar to
  UNIX pipe at the same time
- import/export turned into expressions as well
- removed tuple type, ArgsPack works in places of tuples, and parenthesis
  can not be used to quote assign operation now, it's interpreted as keyword
  argument specification in creating a new apk
- can send and receive symbolic arguments now
- spaces are allowed between @ and attribute name for symbolic attributes
- various bugfixes and improvements

## 0.2.0.0

- class procedure syntax change (breaking old code)
- various improvements

## 0.1.0.1

- fixed a bug that can not start with GHC 8.8
- reactor logic fixup

## 0.1.0.0

- first public release
