# Revision history for edh

## 0.3.0.0

- Compositional Class

  Pre _0.3_, there is only the class procedure, but no class object, version
  _0.3_ introduced the class object (whose class is meta class object).

  **Edh** class is similar to **Python** class in how multiple inheritance
  is supported with
  [C3 linearized](https://en.wikipedia.org/wiki/C3_linearization)
  **mro** list, but unlike **Python**, each super class in the **mro** list
  of an **Edh** class will instantiate a separate object instance, on
  construction from an end **Edh** class. Each object instance is constructed
  with a super object list corresponding to its class' **mro** list, and
  individual constituent objects can be obtained from an end object by
  pattern-matching against the desired super class, this is a bit like
  dynamic upcasting to base class in **C++**.

  As pre _0.3_, an **Edh** object is open to `extends` more super objects
  after constructed from its class.

- Dynamic Scoped Effects

  Keyword `effect` is introduced for effectful artifact registration, and
  `perform` / `behave` introduced for the resolution.

- Exception Handling wrt Structured Concurrency

  _0.3_ comes with a working exception handling mechanism, similar to that
  in **JavaScript** and **Python**.

  Additionally in tackling structured concurrency, spawned threads (go
  routines) will invoke its spawner's exception handler enclosing the
  spawn point, for exceptions not handled by inner _catch_ blocks. While
  _finally_ blocks will never be triggered by spawned threads.

  Especially note that in **Edh**, call frames keep stacking up for a
  spawned thread atop its spawner's call stack, unlike traditional mechanisms
  in most other languages/runtimes adhere to POSIX fork semantics. **Edh**
  made this design choice so as to allow descendant threads to resolve
  dynamic scoped effects against the call stack even cross the thread
  boundaries. And the **hosting pattern** can be used to break call stack
  inheritance, that is technically to have a desirable spawner thread loop
  against an event stream of callable procedures, and spawn the call for
  each one there.

- Preemptive Event Perceiver

  The `reactor` procedure before _0.3_ is dropped, `perceive` keyword is
  introduced since _0.3_ to install a pattern-matching expression (block
  or single branch) against each event value received from an event sink.

  Event perceivers preempt the execution of the trunk sequence of transactions
  on the thread.


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
