# Revision history for edh

## 0.3.0.0

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
