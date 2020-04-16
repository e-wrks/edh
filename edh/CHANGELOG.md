# Revision history for edh

## 0.3.0.0

- exception throwing and handling work now, but using operators instead of
  keyword based syntax
  - `throw` keyword /w syntax unchanged
  - use (`$=>`) as `catch` and (`@=>`) as `finally`
  - originally planned `try`/`catch`/`finally` keywords and syntax dropped
  - exception classes refactored for Edh code to easily handle host errors
- reactor procedure dropped, changed to `perceive` construct, same feature
  but different syntax that breaks old code
- the `runtime` module and its host artifacts from default batteries are
  refactored to be `console` module with an implementation in default
  batteries
- Python compatible syntax:
  - (+) can do string concatenation when left-hand is a string
  - triple quoted strings (backtick as well as single/double quotes)
- bugfixes and improvements

## 0.2.0.0

- class procedure syntax change (breaking old code)
- various improvements

## 0.1.0.1

- fixed a bug that can not start with GHC 8.8
- reactor logic fixup

## 0.1.0.0

- first public release
