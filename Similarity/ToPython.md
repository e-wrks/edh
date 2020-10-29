# Đ (Edh) is similar to **Python** in that:

## Zen

See [The Zen of Python](https://www.python.org/dev/peps/pep-0020)

## Overall Syntax

- Call Operator

  e.g. `f( g( x, y ) )`, where `new` keyword is not
  needed for constructor call (but can be there for compatibility with
  **JavaScript** etc.)

- Dot Notation

  e.g. `obj.attr`, `obj.attr = 3*7`

- Indexing

  e.g. `obj[idx]`, `obj[idx] = 3*7`

- etc. etc.

## First Class Procedures

    Including `=>` to `lambda` functions.

## Dynamicity

...

## Object System

- Class based

  while being prototype based at the same time)

- Multiple Inheritance

  with
  [C3 linearization](https://en.wikipedia.org/wiki/C3_linearization)

- Property by Getter / Setter methods

- Magic Methods

  Class definition syntax and semantics in **Đ (Edh)** are vastly the
  same as in **Python**, e.g. the magic methods `__init__()`, `__str__()`,
  `__repr__()` have exactly the same semantics.

  While in **Python** you can rely on the language to translate `obj + val`
  to `obj.__add__(val)`, `val + obj` to `obj.__radd__(val)`, in **Đ (Edh)**
  the same surface syntax is translated to `obj.(+)(val)` and
  `obj.(+@)(val)` respectively.

  More examples:

| Surface Syntax   | Python Translation          | Đ (Edh) Translation   |
| ---------------- | --------------------------- | --------------------- |
| `obj - val`      | `obj.__sub__(val)`          | `obj.(-)(val)`        |
| `val - obj`      | `obj.__rsub__(val)`         | `obj.(-@)(val)`       |
| `obj(x, y)`      | `obj.__call__(x, y)`        | `obj.__call__(x, y)`  |
| `obj[idx]`       | `obj.__getitem__(idx)`      | `obj.([])(idx)`       |
| `obj[idx] = val` | `obj.__setitem__(idx, val)` | `obj.([=])(idx, val)` |
| `obj += val`     | `obj.__iadd__(val)`         | `obj.(+=)(val)`       |

    While you are limited to operators defined by the language as with
    **Python**, all operators in **Đ (Edh)** are custom operators - some come
    with the default batteries, while it is open for all **Đ** programmers to
    define arbitrary operators as they see fit, then all operators get
    automatically translated to magic methods for objects, making it vastly
    more extensible than **Python**.

## Conditional Operator Implementation

**Đ (Edh)** supports the idiom of `return`ing `default <expr>` from an
operator's implementing method (whether standalone or being some object's
magic method), this is at par to **Python**'s
[NotImplemented](https://docs.python.org/3/library/constants.html#NotImplemented)
semantic, but it is more powerful in that instead of refusal in entirety,
an inferior implementation can be supplied as the `<expr>` as well.
`default nil` carries the same semantic as
[NotImplemented](https://docs.python.org/3/library/constants.html#NotImplemented)
, while there is a literal constant `NA` (stands for **Not/Applicable**)
in **Đ (Edh)** being equivalent to `default nil`.

A standalone operator procedure in **Đ (Edh)** (which **Python** doesn't
have an equivelant) assumes higher priority than a magic method from any
of the operand objects, it is vital for such standalone operators to
`return default <formulae>` in order for objects to be able to override
it with magic methods for more meaningful, superior implementations.

E.g. the `++` and `+` operator come with default batteries are meant
to do string concatenation (as for non-numeric values in case of `+`
operator) after both operands converted with `str()`, but obviously the
`Vector` class wants to override them to return vectorized result with
element-wise operations applied.

And **HasDim** defined `Column` class which is for array objects similar
to 1d **Numpy** `ndarray`, it performs similar overrides to do
vectorized High Performance Numeric Computation against **SIMD** ready
data stored for a column object.

Then a subclass' magic method assumes higher priority than those from some
super classes, so a class can `return` `default <expr>` to prefer super
implementation while providing a fail-safe implementation. This is more
useful when multiple inheritance is in consideration, and as the choice
being dynamically decidable.

## Decorators

`$` is used to express decorators in **Đ (Edh)** (through it is actually
a general procedure-call operator with low precedence), `property$`
and `setter$` e.g. are there for exactly the same semantics as
`@property` and `@setter` in **Python**

## Data Classes ([PEP557](https://www.python.org/dev/peps/pep-0557))

`data` is a dedicated keyword in **Đ (Edh)** to define a class in ways
almost the same as [PEP557](https://www.python.org/dev/peps/pep-0557)
manifests.

## Asynchronous Constructs

[PEP492](https://www.python.org/dev/peps/pep-0492)
[PEP525](https://www.python.org/dev/peps/pep-0525)
[PEP530](https://www.python.org/dev/peps/pep-0530)

## Seamless Integration with the Host Language / Runtime

**Haskell** as for **Đ (Edh)** to **C/C++** as for **Python**

In a sense you can regard **Python** as a surface language for **C/C++**
as well.

## Namespace Modules and Entry Modules

      `__init__.edh` to `__init__.py`

      `__main__.edh` to `__main__.py`

## Reflective Meta Data

      `__name__`, `__file__` etc.

## **Sphinx** based Auto Documentation

## Nice **REPL**
