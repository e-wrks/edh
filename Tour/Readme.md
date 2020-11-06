# A Tour of Đ (Edh)

You want to run a bare **Edh** interpreter (the **REPL**), to play with the
language basics, to develop new batteries merely in **Edh** the surface
language, or do other sorts of fun stuffs. (Note there can be
[File Operating Edh](https://github.com/e-wrks/foedh)
for shell scripting support and other derivatives)

While a real **Haskell** + **Edh** application would certainly include it's
unique **Edh** interpreter with more powerful batteries written in the host
language (i.e. **Haskell**) installed, in addition to the default ones.
See [Edh Im](https://github.com/e-wrks/edhim) for an example.

- [Running the REPL (a bare interpreter)](#running-the-repl-a-bare-interpreter)
  - [Run with verbose (or lean) log level](#run-with-verbose-or-lean-log-level)
  - [Multi / Single line input modes](#multi--single-line-input-modes)
  - [Paste code snippets from this Tour](#paste-code-snippets-from-this-tour)
- [Program / Threading Model](#program--threading-model)
- [Package / Module Structures](#package--module-structures)
  - [Entry Module vs Persistent Module](#entry-module-vs-persistent-module)
- [Micro Structures](#micro-structures)
  - [Importing other Edh modules](#importing-other-edh-modules)
  - [Lossless Decimal for Numbers](#lossless-decimal-for-numbers)
  - [Arguments (Un / Re) Packing](#arguments-un--re-packing)
    - [Compatible with Pythonic arguments](#compatible-with-pythonic-arguments)
    - [pkargs() the utility](#pkargs-the-utility)
    - [Args Unpacking on receiving](#args-unpacking-on-receiving)
    - [Args Repacking on receiving](#args-repacking-on-receiving)
    - [let does args](#let-does-args)
    - [for-from-do loop does args](#for-from-do-loop-does-args)
    - [import does args](#import-does-args)
    - [generator does args](#generator-does-args)
  - [Comprehensions](#comprehensions)
  - [Operators](#operators)
  - [list/dict modification](#listdict-modification)
  - [Tenary](#tenary)
  - [Logging](#logging)
  - [Type Inspections](#type-inspections)
  - [Branches with Value Matching / Pattern Matching](#branches-with-value-matching--pattern-matching)
    - [Value Matching](#value-matching)
    - [Case-Of](#case-of)
    - [Pattern Matching](#pattern-matching)
    - [Branching semantics, Fallthrough](#branching-semantics-fallthrough)
- [Procedures in Action](#procedures-in-action)
  - [Host Procedures](#host-procedures)
  - [Method Procedures](#method-procedures)
  - [Generator Procedures](#generator-procedures)
  - [Interpreter Procedures](#interpreter-procedures)
  - [Class Procedures](#class-procedures)
    - [Inheritance Hierarchy](#inheritance-hierarchy)
      - [Magical Supers](#magical-supers)
      - [More OO Approaches](#more-oo-approaches)
  - [Reactor Procedures](#reactor-procedures)
  - [Producer Procedures](#producer-procedures)
- [Go Routines](#go-routines)
- [Programming Concurrency and Data Consistency as a whole](#programming-concurrency-and-data-consistency-as-a-whole)
- [Event Sink / Reactor / Defer](#event-sink--reactor--defer)
- [Indexing](#indexing)
- [Defining More Magic Methods](#defining-more-magic-methods)
- [Reflections](#reflections)
- [Terminology](#terminology)
  - [World](#world)
  - [Package](#package)
  - [Module](#module)
  - [Entity](#entity)
    - [Attribute](#attribute)
    - [Symbol](#symbol)
  - [Scope](#scope)
  - [No Variable](#no-variable)
    - [Attribute Assignment](#attribute-assignment)
    - [Attribute Read](#attribute-read)
    - [Transactional Semantics Amplification](#transactional-semantics-amplification)
  - [Transaction (STM)](#transaction-stm)
    - [The ai keyword](#the-ai-keyword)
  - [Function (or lack thereof)](#function-or-lack-thereof)
  - [Operator](#operator)
  - [Procedure](#procedure)
    - [Host Procedure](#host-procedure)
      - [Vanilla Host Procedure](#vanilla-host-procedure)
      - [Host Operator Procedure](#host-operator-procedure)
      - [Host Generator Procedure](#host-generator-procedure)
    - [Constructor Procedure](#constructor-procedure)
      - [Class Procedure](#class-procedure)
      - [Module Procedure](#module-procedure)
    - [Method Procedure](#method-procedure)
      - [Vanilla Method Procedure](#vanilla-method-procedure)
      - [Operator Procedure](#operator-procedure)
      - [Generator Procedure](#generator-procedure)
      - [Interpreter Procedure](#interpreter-procedure)
      - [Producer Procedure](#producer-procedure)
  - [Go Routine](#go-routine)
    - [The go keyword](#the-go-keyword)
    - [The defer keyword](#the-defer-keyword)
  - [Event Sink](#event-sink)
    - [The reactor Procedure](#the-reactor-procedure)
    - [Break the thread from reactor](#break-the-thread-from-reactor)
  - [Value / Type](#value--type)
  - [Object / Class](#object--class)
    - [This reference](#this-reference)
    - [That reference](#that-reference)
    - [Super](#super)
  - [EHI (Edh Host Interface)](#ehi-edh-host-interface)

## Running the REPL (a bare interpreter)

```bash
git clone https://github.com/e-wrks/edh
cd edh
```

```shell
cabal v2-install edhi --overwrite-policy=always
```

### Run with verbose (or lean) log level

```shell
export EDH_LOG_LEVEL=DEBUG
# export EDH_LOG_LEVEL=WARN
edhi
```

```shell
$ export EDH_LOG_LEVEL=DEBUG
$ edhi
>> Bare Đ (Edh) Interpreter <<
* Blank Screen Syndrome ? Take the Tour as your companion, checkout:
  https://github.com/e-wrks/edh/tree/master/Tour
Đ:
```

### Multi / Single line input modes

The repl runs in single-line input mode by default, while **unindented**
curly braces start & end multi-line input mode:

```bash
$ edhi
>> Bare Đ (Edh) Interpreter <<
* Blank Screen Syndrome ? Take the Tour as your companion, checkout:
  https://github.com/e-wrks/edh/tree/master/Tour
Đ: a=3
3
Đ: {
Đ|  1: x=1
Đ|  2: y=2
Đ|  3: }
2
Đ: (x, y)
( 1, 2, )
Đ:
```

### Paste code snippets from this Tour

Code in `*.edh` files in this **Tour** directory are designed to be
copy-and-paste-able to the **REPL**, e.g. pasting:

```c++
{
  operator 📣 5 (lhv, rhv) {
    console.info <| rhv ++ ' is telling ' ++ lhv
  }

  operator 🆚 1 (lhv, rhv) {
    console.info <| "🌀 What's the difference?\n     "
      ++ lhv ++ '\n  🆚\n     ' ++ rhv
  }
}

'a tale' 📣 'the goat'

let (a, b) = ( 'Orange', 'Apple', )
a 🆚 b
```

You'll see:

```bash
Đ: {
Đ|  1:   operator 📣 5 (lhv, rhv) {
Đ|  2:     console.info <| rhv ++ ' is telling ' ++ lhv
Đ|  3:   }
Đ|  4:
Đ|  5:   operator 🆚 1 (lhv, rhv) {
Đ|  6:     console.info <| "🌀 What's the difference?\n     "
Đ|  7:       ++ lhv ++ '\n  🆚\n     ' ++ rhv
Đ|  8:   }
Đ|  9: }
<operator: (🆚) 1>
Đ:
Đ: 'a tale' 📣 'the goat'
Đ:
Đ: let (a, b) = ( 'Orange', 'Apple', )
ℹ️ <adhoc>:2:5
the goat is telling a tale
Đ: a 🆚 b
Đ: ℹ️ <adhoc>:6:5
🌀 What's the difference?
     Orange
  🆚
     Apple

Đ:
```

## Program / Threading Model

Each [go](#go-routine) keyword (can be placed anywhere) in **Edh** code
starts a new **Edh** thread.

An **Edh** program consists of a _main_ **Edh** thread and many descendant
**Edh** threads directly or indirectly started from that _main_ thread.

All uncaught errors will be `throwTo` the _main_ thread, causing it to
terminate. And once the _main_ thread terminates, all its descendant threads
will terminate as well. (This is largely different from other runtime
systems, but roughly follows how **GHC** manages processes and threads)

**Edh** threads have **1:1** mapping relationship to **GHC**'s lightweight
threads. Any **Haskell** process hosting **Edh** worlds should have been
compiled with **GHC** `-threaded` option, and launched with proper **RTS**
options controlling the parallelism.

A single **GHC** **RTS** process can run many **Edh** programs conurrently,
against a same or various separate **Edh** [World](#world)s.

Combined with the _main_ thread's program terminating behavior, this provides
a more elegant solution to the _context_ problem, than **Go**'s `context`
mechanism. E.g. each http request handler starts an **Edh** program,
both frameworks and applications can take advantage of **Edh**/**GHC**
concurrency as much as appropriate, and has nothing required to do for
async task cancellation. (While with prevention of resource leakage by
proper usage of [defer](#the-defer-keyword) ).

- About **Go** context from: https://blog.golang.org/context

> At Google, we require that Go programmers pass a Context parameter as
> the first argument to every function on the call path between incoming
> and outgoing requests. This allows Go code developed by many different
> teams to interoperate well. It provides simple control over timeouts and
> cancelation and ensures that critical values like security credentials
> transit Go programs properly.
>
> Server frameworks that want to build on Context should provide
> implementations of Context to bridge between their packages and those
> that expect a Context parameter. Their client libraries would then accept
> a Context from the calling code. By establishing a common interface for
> request-scoped data and cancelation, Context makes it easier for package
> developers to share code for creating scalable services.

## Package / Module Structures

Checkout how [npm](https://www.npmjs.com/) manages
[NodeJS](https://nodejs.org/en/) packages to see the idea for better
dependency management that **Edh** follows.

Checkout the directory/file structure of the mere **Edh** parts of default
batteries [in the edh repository](../edh_modules/)

It's very similar to the deeply-nested
[`node_modules` folder structures](https://nodejs.org/api/modules.html#modules_loading_from_node_modules_folders)
as with [NodeJS](https://nodejs.org), for an **Edh** program, _Just_
translate the following folder/file names:

- `node_modules` -> `edh_modules`
- `index.js` -> `__init__.edh`
- `*.js` -> `*.edh`

_Maybe_ find & replace all occurences according to above rules, then
https://github.com/npm/cli is right ported to manage **Edh** projects
already (kidding).

Note that module `batteries/root` will be imported into root scope of an
**Edh** **world** when default batteries are installed (the most common case
when a **world** is created).

### Entry Module vs Persistent Module

An entry module is always named by a `__main__.edh` file, the name is infered
from the intermediate file path segments from `edh_modules` to that
`__main__.edh`, an entry module won't be registered to the Edh world and not
importable.

Otherwise a `.edh` file names a persistent module, the name is intermediate
file path segments from `edh_modules` to that `.edh` file but with `.edh`
suffix stripped. One special case is `edh_modules/some/path/__init__.edh`,
the module name will be `some/path`.

A persistent module will have a single instance per **Edh** world, loaded &
shared among the world. Subsequent `import` will get everything exported from
that module.

## Micro Structures

### Importing other Edh modules

**import** in **Edh** works similar to `require()` in **JavaScript**, to
import from `*.edh` files from the local filesystem. Note you always don't
include `.edh` file extension name, but the actuall files must have it.

A import path started with `./` (e.g.
`import * './the/path/to/modu_file'`
) is relative path, relative to parent directory of the module file which
contains the very `import` statement. The file must exists at the expected
path, or the import fails.

Otherwise it's absolute import path (e.g.
`import * 'pkg/subpkg/modu_file'`), **Edh** will search local filesystem
for expected path relative to any `edh_modules` directory from the current
working directory upwards. This is to facility the mechanism for any package
to localize its specialized versions of dependencies, while commonly agreed
versions of packages can sit at upper levels as to be shared.

Checkout how [npm](https://www.npmjs.com/) manages
[NodeJS](https://nodejs.org/en/) packages to see the idea.

You use _argument receiving_ semantics and the same syntax to specify
what is expected from the source module, and what goes into local scope.

Remember that artifacts with an alphanumerric name started with underscore
( `_` ) will never be imported (i.e. treated as private to that module),
and if an artifact is a [Symbol](#symbol) value (don't confuse with a
symbolic attribute though), it will neither be imported however named
(symbol values commonly are just alphanumeric named attributes, the name
for itself would better be brief and meaningful, you'd prefer
`obj.@name` over `obj.@_the_hidden_name_`, where you'd have
`name = Symbol('name')` globally in the module)

Using a wild receiver ( `*` ) is suitable to import package local modules,
this is how from within
[edh_modules/batteries/magic/\_\_init\_\_.edh](../edh_modules/batteries/magic/__init__.edh)

```js
import * './arith'
```

to import everything defined in
[edh_modules/batteries/magic/arith.edh](../edh_modules/batteries/magic/arith.edh)

Otherwise you should use keyword argument receiver syntax, and the receiving
need to be _total_, though you can do a wild drop with `**_`

```bash
Đ: import (**ops) 'batteries/magic'
<object: <module>>
Đ: ops
pkargs( *=<operator: (*) 7>, +=<operator: (+) 6>, -=<operator: (-) 6>, /=<operator: (/) 7>, )
Đ: import ((+) as the'plus'op, **_) 'batteries/magic'
<object: <module>>
Đ: the'plus'op
<operator: (+) 6>
Đ: import ((+)) 'batteries/magic'
* 😱 *
💔
📜 <interactive> 🔎 <adhoc>:1:1
💣 Extraneous keyword arguments: * - /
👉 <adhoc>:1:1
Đ:
```

### Lossless Decimal for Numbers

In **JavaScript**, even today, all numbers are `float64`, it puzzled me a while,
before I figured out this is the reason why we can not have `Int64Array`
besides `Int32Array`/`Int16Array`/`Float64Array`/`Float32Array` etc. that
the language simply unable to handle elements from an `Int64Array` if it's
ever provided.

**Python** gives you lossless integers by default, but `float64` for decimal:

```python
>>> 1.1 + 2.2
3.3000000000000003
>>>
```

**Haskell** forces you to choose a type for every number in your program,
normal options including the lossless `Integer`, bounded `Int`, and
precision-lossing `Double`/`Float`:

```haskell
λ> 1.1 + 2.2 :: Double
3.3000000000000003
λ> 1.1 + 2.2 :: Float
3.3000002
λ>
```

And you have `Data.Scientific` for the rescure, but with its own quirks
from practical daily use:

```haskell
λ> :m +Data.Scientific
λ> x = 1.1 + 2.2 :: Scientific
λ> x
3.3
λ> x / 0
*** Exception: Ratio has zero denominator
λ>
```

> Your compiled **Haskell** program will crash on division-by-zero if not
> handled specifically.

Then here's `Data.Lossless.Decimal` from package
[lossless-decimal](../lossless-decimal)

```haskell
λ> x = 1.1 + 2.2 :: Decimal
λ> x
3.3
λ> x / 0
inf
λ> (-x) / 0
-inf
λ> 0/0 :: Decimal
nan
λ> (0/0 :: Decimal) == 0/0
False
λ> pi = Decimal 1 (-40) 31415926535897932384626433832795028841971
λ> pi
3.1415926535897932384626433832795028841971
λ>
```

All numbers in **Edh** are `Data.Lossless.Decimal` from
[lossless-decimal](../lossless-decimal)
, by default and by all means:

```haskell
Đ: x = 1.1 + 2.2
3.3
Đ: x / 0
inf
Đ: -x / 0
-inf
Đ: 0/0
nan
Đ: nan == nan
false
Đ: y = 7/11
7/11
Đ: ( x, y, x * y )
( 3.3, 7/11, 2.1, )
Đ: pi
3.1415926535897932384626433832795028841971
Đ:
```

### Arguments (Un / Re) Packing

`ArgsPack` is an immutable type of values in **Edh**, it is also part of
the **Edh** call convention.

#### Compatible with Pythonic arguments

```python
method f (x, y=10, *ns, c=3, **kwargs) pass

f (3, 7, 21, *[9, 11], name='doer', **{'msg': "you've got it", 'keynum': 2})
```

#### pkargs() the utility

```bash
Đ: type(pkargs)
HostMethodType
Đ:
Đ: apk = pkargs(3,7,5,z=9,y=11)
pkargs( 3, 7, 5, y=11, z=9, )
Đ:
```

#### Args Unpacking on receiving

```bash
Đ: method f (x, y, z, a, b) [x, y, z, a, b]
f
Đ: f (***apk)
[ 3, 11, 9, 7, 5, ]
Đ:
```

#### Args Repacking on receiving

```bash
Đ: method f (*args, **kwargs) [args, kwargs]
f
Đ: f (***apk)
[ pkargs( 3, 7, 5, ), pkargs( y=11, z=9, ), ]
Đ:
Đ: method f (***argspk) { 'full args': argspk }
f
Đ: f (***apk)
{ "full args":pkargs( 3, 7, 5, y=11, z=9, ), }
Đ:
```

#### let does args

```bash
Đ: let (x, y, z, a, b) = (***apk)
Đ: [x, y, z, a, b]
[ 3, 11, 9, 7, 5, ]
Đ:
Đ: let (*args, **kwargs) = (***apk); [args, kwargs]
[ pkargs( 3, 7, 5, ), pkargs( y=11, z=9, ), ]
Đ:
Đ: let (***argspk) = (***apk); { 'full args': argspk }
{ "full args":pkargs( 3, 7, 5, y=11, z=9, ), }
Đ:
```

#### for-from-do loop does args

```bash
Đ: for (x, y, z, a, b) from [apk] do console.info <| [x, y, z, a, b]
Đ: ℹ️ <adhoc>:1:1
[ 3, 11, 9, 7, 5, ]

Đ: for (*args, **kwargs) from [apk] do console.info <| [args, kwargs]
Đ: ℹ️ <adhoc>:1:1
[ pkargs( 3, 7, 5, ), pkargs( y=11, z=9, ), ]

Đ: for (***argspk) from [apk] do console.info <| { 'full args': argspk }
Đ: ℹ️ <adhoc>:1:1
{ "full args":pkargs( 3, 7, 5, y=11, z=9, ), }

Đ:
```

#### import does args

```bash
Đ: import (**magics) 'batteries/magic'
<object: /home/cyue/Wander/e-wrks/edh/edh_modules/batteries/magic>
Đ: magics
pkargs( *=<operator: (*) 7>, -=<operator: (-) 6>, +=<operator: (+) 6>, /=<operator: (/) 7>, )
Đ:
```

#### generator does args

Checkout [argspk.edh](./argspk.edh)

```bash
Đ: {
Đ|  1:   generator g (n) {
Đ|  2:     for i from range(n) do
Đ|  3:       # pack an arguments sender to yield out,
Đ|  4:       # you'd feel it like calling a callback
Đ|  5:       yield pkargs (i, i * i, desc="square of " ++ i)
Đ|  6:   }
Đ|  7:
Đ|  8:   # arguments receiver syntax in for expression,
Đ|  9:   # you'd feel it like defining a callback
Đ| 10:   for (x, y, desc="the result") from g(5) do
Đ| 11:     console.info <| (x ++ ": " ++ desc ++ " is " ++ y)
Đ| 12: }
Đ: ℹ️ <adhoc>:10:3
0: square of 0 is 0
ℹ️ <adhoc>:10:3
1: square of 1 is 1
ℹ️ <adhoc>:10:3
2: square of 2 is 4
ℹ️ <adhoc>:10:3
3: square of 3 is 9
ℹ️ <adhoc>:10:3
4: square of 4 is 16

Đ:
```

### Comprehensions

Check out [comprehension.edh](./comprehension.edh)

You do **list** / **dict** / **tuple** comprehensions in **Edh** with
the _comprehension_ / _concatenation_ operator (**=<**):

The (**=<**) operator does comprehension as well as concatenation by default:

```bash
Đ: [7, 11] =< for n from range(5) do n
[ 7, 11, 0, 1, 2, 3, 4, ]
Đ:
Đ: {'a': 7, 'b': 11} =< for n from range(5) do 'square of '++n : n*n
{ "square of 4":16, "square of 2":4, "square of 3":9, "a":7, "b":11, "square of 0":0, "square of 1":1, }
Đ:
Đ: (31, 17) =< for n from range(5) do n
( 31, 17, 0, 1, 2, 3, 4, )
Đ:
Đ: {} =< for (k,v) from zip(('a', 'b', 'd'), [3, 7]) do k:v
{ "a":3, "b":7, }
Đ:
```

If you would like comprehension be aligned with traditional semantics that only
fresh ones are created, you can do this:

```bash
Đ: import * 'batteries/SeparateConcatAndComprehOp'
<object: /home/cyue/Wander/e-wrks/edh/edh_modules/batteries/SeparateConcatAndComprehOp>
Đ: [3, 7] <=< [2, 9]
[ 3, 7, 2, 9, ]
Đ: [3, 7] =< [2, 9]
* 😱 *
💔
📜 <interactive> 🔎 <adhoc>:1:1
📜 =< 🔎 /home/cyue/Wander/e-wrks/edh/edh_modules/batteries/SeparateConcatAndComprehOp.edh:11:37
📜 error 🔎 <host-code>
💣 You don't comprehend into non-empty ones!
👉 /home/cyue/Wander/e-wrks/edh/edh_modules/batteries/SeparateConcatAndComprehOp.edh:14:5
Đ:
```

### Operators

Check out [operator.edh](./operator.edh)

You can inspect an operator at the REPL, just print it:

```bash
Đ: (++)
<operator: (++) 2>
Đ: (+=)
<operator: (+=) 2>
Đ: type( (++), (+=) )
( HostOperType, OperatorType, )
Đ:
```

All operators can be overridden in **Edh**

```bash
Đ: {
Đ|  1:   method localOverrides * {
Đ|  2:     # overide the (++) operator within this procedure only, avoid
Đ|  3:     # polluting the module scope
Đ|  4:
Đ|  5:     before = 'You' ++ ' and ' ++ 'me'
Đ|  6:     operator ++ (lhv, rhv) {
Đ|  7:       # inside the overriding operator definition, the overridden,
Đ|  8:       # original operator is available as was before the overide
Đ|  9:       lhv ++ ' ⭕ ' ++ rhv
Đ| 10:     }
Đ| 11:     after = 'You' ++ ' and ' ++ 'me'
Đ| 12:
Đ| 13:     before 🆚 after
Đ| 14:   }
Đ| 15: }
localOverrides
Đ:
Đ: localOverrides()
Đ: ℹ️ <adhoc>:6:5
🌀 What's the difference?
     You and me
  🆚
     You ⭕  and  ⭕ me

Đ:
```

Also the implementation of
[SeparateConcatAndComprehOp](../edh_modules/batteries/SeparateConcatAndComprehOp.edh)
demonstrates more operator syntaxes and mechanisms:

```c++
# re-declare (=<) as the concat operator (<=<)
operator <=< 1 () (=<)

# Override operator (=<) to comprehend into empty ones only
operator =< (callerScope, lhe, rhe) {
  lhv = callerScope.eval(lhe)
  if not null(lhv) then
    error("You don't comprehend into non-empty ones!")
  # left-hand value is empty, can do it
  callerScope.eval( makeOp(lhe, "<=<", rhe) )

  # the overridden original (=<) operator is in scope of this proc,
  # but don't do `lhv =< callerScope.eval(rhe)` here, as it won't
  # work as expected when `rhe` is a for-from-do loop
}
```

### list/dict modification

- append to a list/dict
  - just use the comprehension operator as well
- prepend to a list, insert/update single entry to a dict
  - there's the `cons` operator (**=>**) for it

```bash
Đ: let (l, d) = ([3,'foo',5], {'a': 'good', 'b': 9})
Đ: l =< [2,'bar',9]
[ 3, "foo", 5, 2, "bar", 9, ]
Đ: d =< {'b': 1, 'm': 'cool!'}
{ "m":"cool!", "a":"good", "b":1, }
Đ: 'baz' => l
[ "baz", 3, "foo", 5, 2, "bar", 9, ]
Đ: ('n', 'yeah') => d
{ "m":"cool!", "n":"yeah", "a":"good", "b":1, }
Đ:
```

### Tenary

in **C** you do:

```C
onCnd ? oneThing : theOther
```

and in **Python** as well as **Edh** you do it the **Pythonic** way:

```python
onCnd and oneThing or theOther
```

```bash
(repl)Đ: 2 < 1 and 'no way!' or 'of coz'
of coz
```

a difference to **Python** is that in **Edh** an object customize its behavior
with `__null__()` magic method, instead of `__bool__()` as in **Python**

also, in **Edh** you can do it the **Haskellish** way:

```haskell
if onCnd then oneThing else theOther
```

simulating the `Maybe` monad:

```haskell
Đ: {
Đ|  1:   method fetchEgg () Symbol('Egg')
Đ|  2:   method lightFire () true
Đ|  3:   method putPanOnFire () true
Đ|  4:   method putEggInPan () true
Đ|  5:   method getFriedEgg () Symbol('FriedEgg')
Đ|  6:
Đ|  7:   method cookMeal () fetchEgg()
Đ|  8:     and lightFire()
Đ|  9:     and putPanOnFire()
Đ| 10:     and putEggInPan()
Đ| 11:     and getFriedEgg()
Đ| 12:
Đ| 13:   'got meal - ' ++ cookMeal()
Đ| 14: }
got meal - FriedEgg
Đ:
Đ: {
Đ|  1:   method lightFire () Nothing
Đ|  2:   'still got meal - ' ++ cookMeal()
Đ|  3: }
still got meal - Nothing
Đ:
```

### Logging

Logging is done by an operator (**<|**) too, surprise!

`console.xxx` are just number values to specify the target level of
a log record, and the process environment variable `EDH_LOG_LEVEL`
if set, will cause log records with lower target levels be dropped
(not eval'ed at all in fact).

```bash
$ export EDH_LOG_LEVEL=WARN
$ edhi
>> Bare Đ (Edh) Interpreter <<
* Blank Screen Syndrome ? Take the Tour as your companion, checkout:
  https://github.com/e-wrks/edh/tree/master/Tour
Đ: console.debug
10
Đ: console.info
20
Đ: console.warn
30
Đ: console.error
40
Đ: console.fatal
50
Đ:
Đ: console.warn <| "You won't see source location info in log if the level is WARN or higher"
Đ: ⚠️ You won't see source location info in log if the level is WARN or higher
Đ:
$ export EDH_LOG_LEVEL=DEBUG
$ edhi
>> Bare Đ (Edh) Interpreter <<
* Blank Screen Syndrome ? Take the Tour as your companion, checkout:
  https://github.com/e-wrks/edh/tree/master/Tour
Đ: console.info <| "Source location is informative most of the time, right?"
Đ: ℹ️ <adhoc>:1:1
Source location is informative most of the time, right?
Đ: console.debug <| "Especially when trouble shooting some unexpected results."
Đ: 🐞 <adhoc>:1:1
Especially when trouble shooting some unexpected results.
Đ: 50<|'use a number works the same way!'
Đ: 🔥 <adhoc>:1:1
use a number works the same way!
Đ:
```

### Type Inspections

```haskell
Đ: type(7)
DecimalType
Đ: type(3, 'abc', 2:5)
( DecimalType, StringType, PairType, )
Đ: type(type, (+), type(1))
( HostProcType, HostOperType, TypeType, )
Đ: type(pkargs(1,2,k1='a'), type'of'dict={,}, type'of'tuple=(,), type'of'list=[], type'of'nil=nil)
pkargs( ArgsPackType, type'of'dict=DictType, type'of'list=ListType, type'of'nil=nil, type'of'tuple=TupleType, )
Đ:
```

### Branches with Value Matching / Pattern Matching

You may know (**->**) in **Haskell**, it is also in **Edh** but called
the **branch** operator:

```bash
Đ: (->)
<hostop: (->) 0>
Đ: 1 < 2 -> 'it must be!'
it must be!
Đ: 1 > 2 -> 'not the case!'
<fallthrough>
Đ: 'more than truth' -> 'Edh do JavaScript style value coercing?'
<fallthrough>
Đ: _ -> 'the wildcard always matches!'
the wildcard always matches!
Đ:
```

#### Value Matching

`<fallthrough>` is the result value from evaluating a non-matched branch,
it signals the _try-next-case_ semantic. And without an enclosing `case-of`
construct, the _left-hand-value_ to the branch (**->**) operator is matched
against the value `true`. And since **Edh** is strongly typed (though
dynamically typed), there is no _trueish_ semantics for another type of
value to be matched with `true`.

> You'll soon see [Pattern Matching](#pattern-matching), the **branch**
> does [Value Matching](#value-matching) unless **Pattern Matching** is
> invoked by _curly-brace-quoting_ at _left-hand-side_ of the branch
> (**->**) operator.

#### Case-Of

Check out [case-of.edh](./case-of.edh)

To match against some value determined at runtime, you use `case-of`, it
looks and feels the same as `case of` in **Haskell** except not statically
typed.

```bash
Đ: case type('the question', 5) of (StringType, DecimalType) -> 'yeath'
yeath
Đ: case type('the question', 5) of (StringType, StringType) -> 'possible?'
<fallthrough>
```

```bash

Đ:
Đ: {
Đ|  1:   method essay (v) case type(v) of {
Đ|  2:     BoolType -> "to be or not to be, that's a problem"
Đ|  3:
Đ|  4:     DecimalType -> {
Đ|  5:         v<2 -> "consume less, produce more";
Đ|  6:         v<10 -> "no more than " ++ v ++ " cups of coffee a day";
Đ|  7:         _ -> "every one get his/her lucky number"
Đ|  8:     }
Đ|  9:
Đ| 10:     StringType -> {quiz=v fallthrough}
Đ| 11:
Đ| 12:     SymbolType -> {quiz='mistery attracts most people' fallthrough}
Đ| 13:
Đ| 14:     ObjectType -> {
Đ| 15:       quiz = 'I live in ' ++ v?__name__ or 'no where';
Đ| 16:       fallthrough
Đ| 17:     }
Đ| 18:
Đ| 19:     "do you known, that " ++ quiz ++ " ?"
Đ| 20:   }
Đ| 21: }
essay
Đ:
Đ: essay(true)
to be or not to be, that's a problem
Đ:
Đ: essay(1)
consume less, produce more
Đ:
Đ: essay(5)
no more than 5 cups of coffee a day
Đ:
Đ: essay(25)
every one get his/her lucky number
Đ:
Đ: essay('magic happens')
do you known, that magic happens ?
Đ:
Đ: essay(Symbol('hidden-secrete'))
do you known, that mistery attracts most people ?
Đ:
Đ: essay(this)
do you known, that I live in <interactive> ?
Đ:
Đ: class C pass
C
Đ: essay(C())
do you known, that I live in no where ?
Đ:
```

#### Pattern Matching

Check out [patterns.edh](./patterns.edh)

**Pattern Matching** is invoked by _curly-brace-quoting_ at _left-hand-side_
of the branch (**->**) operator.

Patterns available by now:

```bash
Đ: {
Đ|  1:   case 3:2:1 of {
Đ|  2:     { x:y } -> 'pair pattern matches the length'
Đ|  3:     { x:y:z } -> 'so this one fires'
Đ|  4:   }
Đ|  5: }
so this one fires
Đ:
Đ: case 3:2 of { (x:y) } -> 'the pair pattern can be parenthesised'
the pair pattern can be parenthesised
Đ:
Đ: case 3*7-5 of { result } -> 'a wild capture pattern receives the ' ++ result
a wild capture pattern receives the 16
Đ:
Đ: case [7, 3, 5] of { head => tail } -> 'uncons pattern does uncons, got ' ++ (head, tail)
uncons pattern does uncons, got ( 7, [ 3, 5, ], )
Đ:
Đ: case (3, 5, 7) of { (x, y, z) } -> 'tuple pattern matches the length'
tuple pattern matches the length
Đ:
Đ: case (3, 5, 7) of { (x, y) } -> 'tuple pattern matches the length'
<fallthrough>
Đ:
Đ: class B pass
B
Đ: class C extends B()
C
Đ: c = C()
<object: C>
Đ:
Đ: case c of {{ B:b }} -> 'instance resolving pattern obtains the right super instance: ' ++ b
instance resolving pattern obtains the right super instance: <object: B>
Đ:
Đ: case 'b' of {[ 'a', 'b', 'c' ]} -> 'any-of pattern feels like list element-of test'
any-of pattern feels like list element-of test
Đ:
```

And more patterns tend to be added in the future.

#### Branching semantics, Fallthrough

Check out [branch.edh](./branch.edh)

Once a **branch** has its _left-hand-side_ value or pattern matched, its
_right-hand-side_ expression is evaluated, then its immediate enclosing
block is considered to have been evaluated to the result value, without
consulting any following statements in this block; unless the
_right-hand-side_ of the branch (**->**) operator is evaluated to a result
of `<fallthrough>`, in which case the rest statements in the block continue
to be evaluated sequentially.

```bash
Đ: {
Đ|  1:   method countdown(n) case type(n) of {
Đ|  2:
Đ|  3:     DecimalType -> {
Đ|  4:
Đ|  5:       n < 1 -> console.info <| '  🎉 instantly !!'
Đ|  6:
Đ|  7:       n > 5 -> {
Đ|  8:         console.warn <| "  😓 that's too many to count, doing my most ..."
Đ|  9:         n = 5
Đ| 10:         fallthrough # similar to `fallthrough` in Go
Đ| 11:       }
Đ| 12:
Đ| 13:       # (:-) will be parsed as another operator, sep (1 space used below) needed here
Đ| 14:       for i from range(n : 0 : -1) do console.info <| '  ⏲️  ' ++ i
Đ| 15:       console.info <| '  🎉 !!'
Đ| 16:
Đ| 17:     }
Đ| 18:
Đ| 19:     _ -> # the underscore condition always matches, similar to underscore in Haskell
Đ| 20:       console.error <| "I don't know what you want from a " ++ type(n) ++ ': ' ++ n
Đ| 21:
Đ| 22:     console.fatal <| "don't worry, this will never happen."
Đ| 23:   }
Đ| 24: }
countdown
Đ:
Đ: countdown(3)
Đ: ℹ️ <adhoc>:14:7
  ⏲️  3
ℹ️ <adhoc>:14:7
  ⏲️  2
ℹ️ <adhoc>:14:7
  ⏲️  1
ℹ️ <adhoc>:15:7
  🎉 !!

Đ: countdown(50)
Đ: ⚠️ <adhoc>:8:9
  😓 that's too many to count, doing my most ...
ℹ️ <adhoc>:14:7
  ⏲️  5
ℹ️ <adhoc>:14:7
  ⏲️  4
ℹ️ <adhoc>:14:7
  ⏲️  3
ℹ️ <adhoc>:14:7
  ⏲️  2
ℹ️ <adhoc>:14:7
  ⏲️  1
ℹ️ <adhoc>:15:7
  🎉 !!

Đ: countdown(-1)
Đ: ℹ️ <adhoc>:5:7
  🎉 instantly !!

Đ: countdown('the hell')
Đ: ❗ <adhoc>:19:5
I don't know what you want from a StringType: the hell

Đ:
```

## Procedures in Action

### Host Procedures

Host procedures are written in the host language (i.e. **Haskell**),
e.g.

```haskell
-- | utility null(*args,**kwargs) - null tester
isNullProc :: EdhProcedure
isNullProc !argsSender !exit = do
  !pgs <- ask
  packEdhArgs argsSender $ \(ArgsPack !args !kwargs) -> if null kwargs
    then case args of
      [v] -> contEdhSTM $ do
        isNull <- EdhBool <$> edhValueNull v
        exitEdhSTM pgs exit isNull
      _ -> contEdhSTM $ do
        argsNulls <- sequence $ ((EdhBool <$>) . edhValueNull) <$> args
        exitEdhSTM pgs exit (EdhTuple argsNulls)
    else contEdhSTM $ do
      argsNulls   <- sequence $ ((EdhBool <$>) . edhValueNull) <$> args
      kwargsNulls <- sequence $ Map.map ((EdhBool <$>) . edhValueNull) kwargs
      exitEdhSTM pgs exit (EdhArgsPack $ ArgsPack argsNulls kwargsNulls)
```

```haskell
-- | operator (:) - pair constructor
consProc :: EdhProcedure
consProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit = do
  pgs <- ask
  -- make sure left hand and right hand values are evaluated in same tx
  local (const pgs { edh'in'tx = True })
    $ evalExpr lhExpr
    $ \(OriginalValue !lhVal _ _) ->
        evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
          contEdhSTM $ exitEdhSTM pgs exit (EdhPair lhVal rhVal)
consProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)
```

```haskell
timelyNotify :: Int -> EdhGenrCaller -> STM ()
timelyNotify !delayMicros genr'caller@(!pgs', !iter'cb) = do
  nanos <- (toNanoSecs <$>) $ unsafeIOToSTM $ do
    threadDelay delayMicros
    getTime Realtime
  -- yield the nanosecond timestamp to iterator
  runEdhProc pgs' $ iter'cb (EdhDecimal $ fromInteger nanos) $ \_ ->
    timelyNotify delayMicros genr'caller

-- | host generator console.everyMicros(n) - with fixed interval
rtEveryMicrosProc :: EdhProcedure
rtEveryMicrosProc !argsSender _ = ask >>= \pgs ->
  case generatorCaller $ edh'context pgs of
    Nothing          -> throwEdh EvalError "Can only be called as generator"
    Just genr'caller -> case argsSender of
      [SendPosArg !nExpr] -> evalExpr nExpr $ \(OriginalValue nVal _ _) ->
        case nVal of
          (EdhDecimal (Decimal d e n)) | d == 1 ->
            contEdhSTM $ timelyNotify (fromIntegral n * 10 ^ e) genr'caller
          _ -> throwEdh EvalError $ "Invalid argument: " <> T.pack (show nVal)
      _ ->
        throwEdh EvalError $ "Invalid argument: " <> T.pack (show argsSender)
```

### Method Procedures

e.g. checkout [str.edh](../edh_modules/batteries/root/str.edh)

```javascript
method join(fst, *rest, sep=', ') {
  s = '' ++ fst # do coerce to string now, in case only one arg passed
  for one from rest do s = s ++ sep ++ one
  s
}
```

```bash
Đ: join(3,5,7)
3, 5, 7
Đ:
Đ: join('I','am','good', sep=' ')
I am good
Đ:
```

### Generator Procedures

Checkout [generator.edh](./generator.edh)

A generator procedure can only be called by a `for-from-do` loop, facilitating
single producer, single consumer event streaming with backpressure.

Values can be exchanged between the generator and the `do` expr

```bash
Đ: generator ss n while true n = yield n*n
ss
Đ: for n from ss(3) do { console.info<|n; if n > 100 then break else n }
Đ: ℹ️ <adhoc>:1:23
9
ℹ️ <adhoc>:1:23
81
ℹ️ <adhoc>:1:23
6561

Đ:
```

The `for-from-do` loop is an expression, and its final value evaluates to the
return value of the generator procedure as invoked:

```bash
Đ: {
Đ|  1:
Đ|  2:   generator g () {
Đ|  3:     yield 1
Đ|  4:     yield 2
Đ|  5:     return 3
Đ|  6:   }
Đ|  7:
Đ|  8:   result = for n from g() do console.info <| 'got ' ++ n
Đ|  9:
Đ| 10:   console.info <| 'Result is: ' ++ result
Đ| 11: }
Đ: ℹ️ <adhoc>:8:3
got 1
ℹ️ <adhoc>:8:3
got 2
ℹ️ <adhoc>:10:3
Result is: 3

Đ:
```

```bash
Đ: {
Đ|  1:   generator g() {
Đ|  2:
Đ|  3:     # a `yield` expression in a generator procedure evals to:
Đ|  4:     #   *) `return nil` on `break` from do block of the loop
Đ|  5:     #   *) `return {return val}` on `return val` from do block of the loop
Đ|  6:     #   *) exception from do block of the loop re-thrown from its position
Đ|  7:
Đ|  8:     case yield 'something' of {
Đ|  9:       { return nil } -> {
Đ| 10:         console.info<| 'the do block broke the for loop'
Đ| 11:         return nil  # cooperate nicely,
Đ| 12:         # or cast black magic if you wish
Đ| 13:       }
Đ| 14:       { return rtn } -> {
Đ| 15:         console.info<| 'early returning from do block: ' ++ rtn
Đ| 16:         return rtn  # cooperate nicely,
Đ| 17:         # or cast black magic if you wish
Đ| 18:       }
Đ| 19:       { xchg'val } -> {
Đ| 20:         console.info<| 'the do block sent ' ++ xchg'val ++ " to generator's yield"
Đ| 21:       }
Đ| 22:       console.info<| 'the do block continued the for loop'
Đ| 23:     }
Đ| 24:
Đ| 25:   }
Đ| 26: }
g
Đ:
Đ: for _ from g() do { pass }
ℹ️ <console>:22:7
the do block continued the for loop
Đ:
Đ: for _ from g() do { continue }
ℹ️ <console>:22:7
the do block continued the for loop
Đ:
Đ: for _ from g() do { break }
ℹ️ <console>:10:9
the do block broke the for loop
Đ:
Đ: for _ from g() do { return 'otherthing' }
ℹ️ <console>:15:9
early returning from do block: <return: "otherthing">
<return: "otherthing">
Đ:
```

Also checkout how the `range()` clone from **Python** is
[implemented in **Edh**](../edh_modules/batteries/root/iter.edh) :

```js
  # resembles `range` in Python
  generator range(start, stop=None, step=None) {

    if None == stop && None == step then case start of {
      # enable the hidden *Edhic* version of `range` using pair
      {(start:stop:step)} -> {fallthrough}
      {(start:stop)} -> {fallthrough}
    }

    if None == stop then let (stop, start) = (start, 0)
    start == stop -> { return nil }
    n = start

    start < stop -> {
      if None == step
        then step = 1
        else if step <= 0 then {
          console.warn <| 'step of ' ++ step ++ ' for range [' ++
                          start ++ ', ' ++ stop ++ ") won't converge"
          return nil
        }
      while n < stop {
        yield n
        n += step
      }
    }

    start > stop -> {
      if None == step
        then step = -1
        else if step >= 0 then {
          console.warn <| 'step of ' ++ step ++ ' for range [' ++
                          start ++ ', ' ++ stop ++ ") won't converge"
          return nil
        }
      while n > stop {
        yield n
        n += step
      }
    }
  }
```

This is pasteable to the REPL:

```python
{
  # Python style `range` (range is a generator procedure in Edh)
  for n from range(5) do console.info <| ' ** iter # ' ++ n
  for n from range(3, 7) do console.info <| ' ** iter # ' ++ n
  for n from range(7, 3) do console.info <| ' ** iter # ' ++ n
  for n from range(5, 10, 2) do console.info <| ' ** iter # ' ++ n
  for n from range(10, 5, -2) do console.info <| ' ** iter # ' ++ n

  # non-converging ranges won't loop
  for n from range(5, 10, -2) do console.info <| ' ** iter # ' ++ n
  for n from range(10, 5, 2) do console.info <| ' ** iter # ' ++ n

  # using pairs
  for n from range(5:10:2) do console.info <| ' ** iter # ' ++ n
  for n from range(7:3) do console.info <| ' ** iter # ' ++ n

  # Python style `enumerate`
  for (i, n) from enumerate(range, 5) do console.info <| ' # ' ++ i ++ ' >> ' ++ n
}
```

### Interpreter Procedures

Check out [interpreter.edh](./interpreter.edh)

```bash
Đ: {
Đ|  1:
Đ|  2:   interpreter lazy(callerScope, x) {
Đ|  3:     method lazyEval () callerScope.eval(x)
Đ|  4:   }
Đ|  5:
Đ|  6:   a = 5; b = 3
Đ|  7:   sum = lazy(a + b)
Đ|  8:
Đ|  9:   console.info <| " once upon a time it's " ++ sum()
Đ| 10:
Đ| 11:   a = 7
Đ| 12:   console.info <| " then later it's " ++ sum()
Đ| 13:
Đ| 14: }
Đ: ℹ️ <adhoc>:9:3
 once upon a time it's 8
ℹ️ <adhoc>:12:3
 then later it's 10

Đ:
```

This is by far a much under explored area in **Edh**, it's supposed to
be the rival of
[Decorators in Python](https://wiki.python.org/moin/PythonDecorators)

And maybe a rival of
[Macros in Julia](https://docs.julialang.org/en/v1/manual/metaprogramming/#man-macros-1)
? Though never in performance-wise respects.

### Class Procedures

Checkout [simple-class.edh](./simple-class.edh)

```bash
Đ: {
Đ|  1:
Đ|  2:   class C {
Đ|  3:     method __init__ (a as this.a) pass
Đ|  4:
Đ|  5:     b = 5
Đ|  6:     method f (n) n*a/b
Đ|  7:     method g (n) { v = (n+3)/a; return v*b}
Đ|  8:
Đ|  9:     method setA(a as this.a) pass
Đ| 10:     method setB(b as this.b) pass
Đ| 11:   }
Đ| 12:
Đ| 13:   c = C(17); # this semicolon is necessary,
Đ| 14:   # or the following tuple will parse as a call
Đ| 15:   # against the assignment result, which is the
Đ| 16:   # newly constructed C object.
Đ| 17:
Đ| 18:   ( c.f(7) , c.g(7) )
Đ| 19:
Đ| 20: }
( 119/5, 50/17, )
Đ:
Đ: c.setA(11); c.setB(23)
Đ:
Đ: ( c.f(7) , c.g(7) )
( 77/23, 230/11, )
Đ:
Đ: c.b = 3
3
Đ:
Đ: ( c.f(7) , c.g(7) )
( 77/3, 30/11, )
Đ:
```

#### Inheritance Hierarchy

Many don't consider **Go** ([GoLang](https://golang.org)) (and **Rust**
similarly in this respect) an _Object Oriented_ programming language,
neither is **Edh** under the same conception. **Edh** does pointer-wise
[Type Embedding](https://go101.org/article/type-embedding.html)
in **Go** spirit.

And **Edh** takes a small step further to offer `that`
reference, which refers to a descendant record from an ancestor
method, in addition to `this` reference which refers to the lexical
self record.

##### Magical Supers

Checkout [magical-supers.edh](./magical-supers.edh), note you can only
run that with master branch (considered nightly) of **Edh** interpreter,
released versions have not support of it.

This is under heavy prototyping with a (not publicly visible) in-memory
graph database project, will be described more clearly later.

##### More OO Approaches

Trying to do traditional style object oriented inheritance is problematic:

Checkout [inheritance.edh](./inheritance.edh)

```bash
Đ: {
Đ|  1:
Đ|  2:   class B {
Đ|  3:       method __init__ (name as this.name) pass
Đ|  4:
Đ|  5:       method greeting(guest) {
Đ|  6:           console.info <| ("Hello "++guest++", I am "++name++', your guide.')
Đ|  7:       }
Đ|  8:   }
Đ|  9:
Đ| 10:   class C {
Đ| 11:       extends B('Nobleman')
Đ| 12:   }
Đ| 13:
Đ| 14:   class D {
Đ| 15:       extends B('Farmer')
Đ| 16:
Đ| 17:       method hello() {
Đ| 18:           console.info <| (`Hello there!`)
Đ| 19:       }
Đ| 20:   }
Đ| 21:
Đ| 22:   class E {
Đ| 23:       extends C()
Đ| 24:       extends D()
Đ| 25:       # an E object will contain 2 copies of B object,
Đ| 26:       # the order above matters in resolving the `greeting` method.
Đ| 27:   }
Đ| 28:
Đ| 29: }
E
Đ:
Đ: e = E()
<object: E>
Đ:
Đ: supers(e)
( <object: D>, <object: C>, )
Đ:
Đ: e.hello()
Đ: ℹ️ <adhoc>:18:11
Hello there!

Đ: e.greeting('New Comer')
Đ:
Đ: embededD = case e of {{ D:d }} -> d
ℹ️ <adhoc>:6:11
Hello New Comer, I am Farmer, your guide.
<object: D>
Đ: embededD.hello()
Đ:
Đ: d = D()
ℹ️ <adhoc>:18:11
Hello there!
<object: D>
Đ: case d of {{ C:c }} -> c
<fallthrough>
Đ:
Đ: embededC = case e of {{ C:c }} -> c
<object: C>
Đ: embededC.hello()
* 😱 *
💔
📜 <interactive> 🔎 <adhoc>:1:1
💣 No such attribute AttrByName "hello" from <object: C>
👉 <adhoc>:1:1
Đ:
```

Otherwise `that` reference is not very useful alone, as you can barely make
any assumption about the record it points to. Well further ideas to leverage
the inheritance constructs so far may include:

- Use symbols to augment `that` descendant record from ancestor methods

  If two modules each defines their own `name = Symbol('name')` symbol,
  assign and use `that.@name = xxx`, there's no clash at all, the
  augmented symbolic attributes are neither visible to irrelevant
  parties at all.

- Make several super classes knowing eachother well, for end classes to
  selectively `extends` a combination of them, then any of them can use
  `case that of {{ FriendClass:friendInst }} ->` to work with allied
  records, along with `this` self record.

- Document the expected behavior / attribute set by ancestor classes for
  decendant classes to follow. Personally I don't like this idea, but it
  is trivially doable.

### Reactor Procedures

A **reactor procedure** is a [Method Procedure](#method-procedure) per se,
what makes it special is that it is not bound to a **scope** (as an
attribute of the **scope** **entity**), instead, it is associated with an
[Event Sink](#event-sink) and attached to a running **Edh** **thread**
(**go** routine).

See [Event Sink / Reactor / Defer](#event-sink--reactor--defer) for its
usage in action.

### Producer Procedures

Checkout [producer.edh](./producer.edh)

A producer procedure is always run from a separate thread forked when it's
called, faciliating multiple event streaming without backpressure, with
possibly multiple producers and multiple consumers.

See [Producer Procedure](#producer-procedure)

```bash
Đ: {
Đ|  1:
Đ|  2:   # a producer procedure always runs in a forked thread, its return
Đ|  3:   # value will be ignored anyway, but its caller will always receive
Đ|  4:   # a `sink` as if returned by the producer procedure.
Đ|  5:   #
Đ|  6:   # the `sink` will be passed to the producer procedure as `outlet`
Đ|  7:   # arg as well, so the caller acts as the consumer of this producer.
Đ|  8:   producer timelyAlert (
Đ|  9:     interval,
Đ| 10:
Đ| 11:     # the `outlet` arg is always filled, if not explicitly passed by
Đ| 12:     # the caller, Edh will create a new `sink`, to be returned to the
Đ| 13:     # caller as well as passed to this producer procedure as `outlet`.
Đ| 14:     outlet=sink
Đ| 15:     # have it a default value to fool the lint/IDE tooling to believe
Đ| 16:     # it's an optional argument for the caller. this is not necessary
Đ| 17:     # for correct behavior though.
Đ| 18:   ) {
Đ| 19:     # no event will be missing for the first consumer (via for-from-do
Đ| 20:     # loop), as this procedure will only get actually running *after*
Đ| 21:     # the first consumer started receiving events from `outlet`.
Đ| 22:     outlet <- 'start alerting you every ' ++ interval ++ ' second(s) ...'
Đ| 23:     for ts from console.everySeconds(interval) do
Đ| 24:       outlet <- '⏰ alarm @@ ' ++ ts
Đ| 25:   }
Đ| 26:
Đ| 27: }
timelyAlert
Đ:
Đ: {
Đ|  1:
Đ|  2:   n = 1
Đ|  3:   for notif from timelyAlert(1) do {
Đ|  4:     console.info<| ' ALARM #' ++ n ++ ' - ' ++ notif
Đ|  5:     if (n+=1) > 3 then { break }
Đ|  6:   }
Đ|  7:
Đ|  8: }
ℹ️ <adhoc>:4:5
 ALARM #1 - start alerting you every 1 second(s) ...
ℹ️ <adhoc>:4:5
 ALARM #2 - ⏰ alarm @@ 1.584071853155282515e18
Đ: ℹ️ <adhoc>:4:5
 ALARM #3 - ⏰ alarm @@ 1.584071854156773843e18

Đ:
```

## Go Routines

Checkout [goroutine.edh](./goroutine.edh)

```bash
Đ: {
Đ|  1:
Đ|  2:   n = 0
Đ|  3:   go for nanos from console.everySeconds(1) do console.info
Đ|  4:         <| '  ⏰ tick#' ++ (n+=1) ++ ' ⏲️  ' ++ nanos ++ 'ns'
Đ|  5:
Đ|  6:   # after main thread terminated, all forked descendant threads
Đ|  7:   # will be terminated along with the Edh program too
Đ|  8:   for _ from console.everySeconds(5) do { break }
Đ|  9:
Đ| 10: }
ℹ️ <adhoc>:3:3
  ⏰ tick#1 ⏲️  1.58403548958834931e18ns
ℹ️ <adhoc>:3:3
  ⏰ tick#2 ⏲️  1.58403549058993302e18ns
ℹ️ <adhoc>:3:3
  ⏰ tick#3 ⏲️  1.584035491591482713e18ns
ℹ️ <adhoc>:3:3
  ⏰ tick#4 ⏲️  1.584035492593035501e18ns
Đ:
```

## Programming Concurrency and Data Consistency as a whole

> When coding within an **Edh** world, you can forget about all kinds of
> [synchronization primitives](http://www.cs.columbia.edu/~hgs/os/sync.html)
> scattered
> [here](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/pthread.h.html),
> [here](https://golang.org/pkg/sync),
> and many _otherwheres_ , with every methods you attempt to program concurrency
> otherwise.
>
> Despite of many **async** frameworks trying to mitigate that disputable
> complexity, e.g.
> [async in JavaScript](https://caolan.github.io/async),
> [asyncio in Python](https://docs.python.org/3/library/asyncio.html),
> and [async in Haskell](http://hackage.haskell.org/package/async).

Checkout the implementation of
[concur](../edh_modules/batteries/root/concur.edh)
and [concur.edh in the Tour using that](./concur.edh).

`concur()` is just an example, it's straight forward for you to write application
logics in similar ways.

```bash
Đ: {
Đ|  1:
Đ|  2:   # fake some time costing works to do
Đ|  3:   generator allWorksToDo(nJobs=10, leastSeconds=3) {
Đ|  4:
Đ|  5:     # use this proc to capture a local copy of the arguments for the task
Đ|  6:     method longthyWork(job'num, seconds2take) {
Đ|  7:       # this anonymous nullary proc defines the task in form of niladic computation
Đ|  8:       method _ () {
Đ|  9:         console.info <| '  🏎️  #' ++ job'num ++ ' started'
Đ| 10:         n = 0
Đ| 11:         for nanos from console.everySeconds(1) do if (n+=1) >= seconds2take
Đ| 12:           then {
Đ| 13:             console.info <| '  🏁  #' ++ job'num ++ ' done'
Đ| 14:             break
Đ| 15:           } else {
Đ| 16:             # uncomment line below to see even more verbose log
Đ| 17:             console.info <| '  📝  #' ++ job'num ++ ' tick ' ++ nanos
Đ| 18:           }
Đ| 19:       }
Đ| 20:     }
Đ| 21:
Đ| 22:     for n from range(nJobs) do yield longthyWork(n, leastSeconds + n)
Đ| 23:   }
Đ| 24:
Đ| 25: }
allWorksToDo
Đ:
Đ: {
Đ|  1:
Đ|  2: {#
Đ|  3:   # `concur()` is the sorta primitive for concurrency scheduling,
Đ|  4:   # it's a plain Edh method procedure defined in `batteries/root`
Đ|  5:   # module so automically available in a Edh world, its signature
Đ|  6:   # looks like following:
Đ|  7:
Đ|  8:   method concur(*tasks, c=6, dbgLogger=0) {
Đ|  9:     ...
Đ| 10:   }
Đ| 11: #}
Đ| 12:
Đ| 13:   concur(
Đ| 14:
Đ| 15:     * (,) =< for work from allWorksToDo(10, 3) do work,
Đ| 16: #   ^--^--^------positional arguments unpacking
Đ| 17: #      |--+------tuple comprehension target/tag
Đ| 18: #         |------comprehension operator in Edh
Đ| 19:
Đ| 20:     c=5, dbgLogger=console.info,
Đ| 21: #    ^------------^---------------keyword arguments
Đ| 22:
Đ| 23:   )
Đ| 24: }
ℹ️ <adhoc>:9:9
  🏎️  #0 started
ℹ️ <adhoc>:9:9
  🏎️  #1 started
ℹ️ <adhoc>:9:9
  🏎️  #2 started
ℹ️ <adhoc>:9:9
  🏎️  #3 started
ℹ️ <adhoc>:9:9
  🏎️  #4 started
ℹ️ <adhoc>:17:13
  📝  #3 tick 1.584036045605982177e18
ℹ️ <adhoc>:17:13
  📝  #2 tick 1.584036045606286008e18
ℹ️ <adhoc>:17:13
  📝  #1 tick 1.584036045606457333e18
ℹ️ <adhoc>:17:13
  📝  #0 tick 1.584036045606627563e18
ℹ️ <adhoc>:17:13
  📝  #4 tick 1.584036045605940946e18
ℹ️ <adhoc>:17:13
  📝  #0 tick 1.58403604660768493e18
ℹ️ <adhoc>:17:13
  📝  #1 tick 1.584036046607955259e18
ℹ️ <adhoc>:17:13
  📝  #2 tick 1.58403604660843663e18
ℹ️ <adhoc>:17:13
  📝  #3 tick 1.584036046608599326e18
ℹ️ <adhoc>:17:13
  📝  #4 tick 1.584036046607649489e18
ℹ️ <adhoc>:17:13
  📝  #3 tick 1.584036047609439892e18
ℹ️ <adhoc>:17:13
  📝  #2 tick 1.584036047609659296e18
ℹ️ <adhoc>:17:13
  📝  #1 tick 1.584036047609800474e18
ℹ️ <adhoc>:13:13
  🏁  #0 done
ℹ️ <adhoc>:9:9
  🏎️  #5 started
ℹ️ <adhoc>:17:13
  📝  #4 tick 1.584036047609387539e18
ℹ️ <adhoc>:17:13

...

ℹ️ /home/cyue/Wander/e-wrks/edh/edh_modules/batteries/root/concur.edh:83:5
  ⏲️  finishing up concur tasks, 2 still running.
ℹ️ <adhoc>:17:13
  📝  #8 tick 1.584036059629547698e18
ℹ️ <adhoc>:17:13
  📝  #9 tick 1.584036060630714579e18
ℹ️ <adhoc>:17:13
  📝  #8 tick 1.584036060630699973e18
ℹ️ <adhoc>:17:13
  📝  #9 tick 1.584036061632301518e18
ℹ️ <adhoc>:13:13
  🏁  #8 done
ℹ️ /home/cyue/Wander/e-wrks/edh/edh_modules/batteries/root/concur.edh:83:5
  ⏲️  finishing up concur tasks, 1 still running.
ℹ️ <adhoc>:17:13
  📝  #9 tick 1.584036062633883264e18
Đ: ℹ️ <adhoc>:13:13
  🏁  #9 done
ℹ️ /home/cyue/Wander/e-wrks/edh/edh_modules/batteries/root/concur.edh:80:5
  🎉  all concur tasks done.

Đ:
```

## Event Sink / Reactor / Defer

See [The reactor Procedure](#the-reactor-procedure) in the
[Terminology](#terminology) section for the mechanism how it works.

Checkout [reactor.edh](./reactor.edh)

```bash
Đ: {
Đ|  1:   evs = sink
Đ|  2:   stopSig = sink
Đ|  3:
Đ|  4:   go {
Đ|  5:
Đ|  6:     defer {
Đ|  7:       console.info <| "I'm really done."
Đ|  8:     }
Đ|  9:
Đ| 10:     reactor stopSig ev {
Đ| 11:       console.info <| '  🎬  stopping because: ' ++ ev
Đ| 12:       break  # break from a reactor terminates the thread
Đ| 13:     }
Đ| 14:
Đ| 15:     for ev from evs do {
Đ| 16:       console.info <| '  🎐  sth happening: ' ++ ev
Đ| 17:     }
Đ| 18:
Đ| 19:   }
Đ| 20:
Đ| 21:   # wait a second
Đ| 22:   for _ from console.everySeconds(1) do { break }
Đ| 23:
Đ| 24:   evs <- '  🛎️  ding.ding..'
Đ| 25:
Đ| 26:   # wait a second
Đ| 27:   for _ from console.everySeconds(1) do { break }
Đ| 28:
Đ| 29:   # stopSig <- "don't do that!"
Đ| 30:
Đ| 31:   evs <- '  🍃  chill..chill...'
Đ| 32:
Đ| 33:   # wait a second
Đ| 34:   for _ from console.everySeconds(1) do { break }
Đ| 35:
Đ| 36:   stopSig <- "that's enough!"
Đ| 37:
Đ| 38:   evs <- '  ☎️  ling.ling..ling...'
Đ| 39:
Đ| 40:   # all descendant threads (go routines) will be terminated when
Đ| 41:   # main thread terminates, need wait here to see any event above
Đ| 42:   # being processed.
Đ| 43:   for _ from console.everySeconds(1) do { break }
Đ| 44:   # console.info <| 'main program terminating ...'
Đ| 45: }
ℹ️ <adhoc>:16:7
  🎐  sth happening:   🛎️  ding.ding..
ℹ️ <adhoc>:16:7
  🎐  sth happening:   🍃  chill..chill...
ℹ️ <adhoc>:11:7
  🎬  stopping because: that's enough!
ℹ️ <adhoc>:7:7
I'm really done.
Đ:
```

## Indexing

Checkout [indexable.edh](./indexable.edh)

This is meant to attract people to port **Pandas** and **Numpy** to
**Haskell** with the aid of **Edh**.

```bash
Đ: {
Đ|  1:   class Data {
Đ|  2:
Đ|  3:     data = {}
Đ|  4:
Đ|  5:     # magic method responding to read with an index
Đ|  6:     method ([]) (ix) {
Đ|  7:
Đ|  8:       # console.info <| 'Indexing with ' ++ type(ix) ++ ': ' ++ ix
Đ|  9:
Đ| 10:       case ix of {
Đ| 11:
Đ| 12:         {(start:stop:step)} -> {
Đ| 13:           console.info <| 'Indexing interleaved 1d range: ' ++ ix
Đ| 14:           break # no way to be success on a dict
Đ| 15:         }
Đ| 16:
Đ| 17:         {(start:stop)} -> {
Đ| 18:           console.info <| 'Indexing contiguous 1d range: ' ++ ix
Đ| 19:           break # no way to be success on a dict
Đ| 20:         }
Đ| 21:
Đ| 22:         {(dim'1, dim'2)} -> {
Đ| 23:
Đ| 24:           console.info <| 'Indexing 2d space with: ' ++ ix
Đ| 25:
Đ| 26:           case dim'1 of {
Đ| 27:             {(start:stop:step)} -> {
Đ| 28:               console.info <| 'Indexing interleaved 1st dimension range: ' ++ dim'1
Đ| 29:               break # no way to be success on a dict
Đ| 30:             }
Đ| 31:
Đ| 32:             {(start:stop)} -> {
Đ| 33:               console.info <| 'Indexing contiguous 1st dimension range: ' ++ dim'1
Đ| 34:               break # no way to be success on a dict
Đ| 35:             }
Đ| 36:           }
Đ| 37:
Đ| 38:           # similar can be done for 2nd dimension - dim'2
Đ| 39:
Đ| 40:           break # no way to be success on a dict
Đ| 41:         }
Đ| 42:
Đ| 43:       }
Đ| 44:
Đ| 45:       case type(ix) of {
Đ| 46:         DecimalType -> {
Đ| 47:           console.info <| 'Indexing 1d element: ' ++ ix
Đ| 48:         }
Đ| 49:         StringType -> {
Đ| 50:           console.info <| 'Indexing column by name: ' ++ ix
Đ| 51:         }
Đ| 52:         _ -> {
Đ| 53:           console.info <| 'Suspicious index ' ++ type(ix) ++ ': ' ++ ix
Đ| 54:           break # avoid actually doing indexing with this ix
Đ| 55:         }
Đ| 56:       }
Đ| 57:
Đ| 58:       this.data[ix]
Đ| 59:     }
Đ| 60:
Đ| 61:     # magic method responding to write with an index
Đ| 62:     method ([=]) (ix, val) this.data[ix] = val
Đ| 63:
Đ| 64:   }
Đ| 65: }
<class: Data>
Đ:
Đ: d = Data()
<object: Data>
Đ:
Đ: d[3] = 5
5
Đ: d[3]
5
Đ: ℹ️ <adhoc>:47:11
Indexing 1d element: 3
Đ: d['price'] = [1.2,1.3,1.1]
[ 1.2, 1.3, 1.1, ]
Đ: d['price']
[ 1.2, 1.3, 1.1, ]
Đ: ℹ️ <adhoc>:50:11
Indexing column by name: price
Đ: d[3:5] = 7
* 😱 *
💔
📜 <interactive> 🔎 <adhoc>:1:1
📜 [=] 🔎 <adhoc>:62:28
💣 Invalid dict key: PairType: 3:5
👉 <adhoc>:62:28
Đ:
Đ: d[3:5]
Đ: ℹ️ <adhoc>:18:11
Indexing contiguous 1d range: 3:5
Đ: d[3:5:2, 0:7:3]
Đ: ℹ️ <adhoc>:24:11
Indexing 2d space with: ( 3:5:2, 0:7:3, )
ℹ️ <adhoc>:28:15
Indexing interleaved 1st dimension range: 3:5:2
Đ: d[3, 5, 7]
Đ: ℹ️ <adhoc>:53:11
Suspicious index TupleType: ( 3, 5, 7, )
Đ:
```

## Defining More Magic Methods

Checkout [./magic.edh](./magic.edh)
[batteries/magic/](../edh_modules/batteries/magic/)
and
[arith.edh](../edh_modules/batteries/magic/arith.edh)

This is meant to attract people to port **Theano** and **TensorFlow** as well as
**Pandas** and **Numpy** to **Haskell** with the aid of **Edh**, while
[AccelerateHS](http://hackage.haskell.org/package/accelerate) and
[Repa](http://hackage.haskell.org/package/repa)
have demonstrated how great **Haskell** can be at heavy lifting wrt number
crunchings.

```bash
Đ: import * 'batteries/magic'
<object: /home/cyue/Wander/e-wrks/edh/edh_modules/batteries/magic>
Đ:
Đ: {
Đ|  1:
Đ|  2:   class Tensor {
Đ|  3:
Đ|  4:     method __init__ (name as this.name) pass
Đ|  5:
Đ|  6:     method (+) (other) case type(other) of {
Đ|  7:       # add to a constant
Đ|  8:       DecimalType -> Tensor(name= '('++ this.name ++ '+' ++ other ++')')
Đ|  9:
Đ| 10:       case other of {{ Tensor:_ }} -> {
Đ| 11:         # add to another Tensor
Đ| 12:         return Tensor(name= '('++ this.name ++ '+' ++ other.name ++')')
Đ| 13:       }
Đ| 14:
Đ| 15:       continue # as NotImplemented in Python
Đ| 16:     }
Đ| 17:
Đ| 18:     method (*) (other) case type(other) of {
Đ| 19:       # mul to a constant
Đ| 20:       DecimalType -> Tensor(name= '('++ this.name ++ '*' ++ other ++')')
Đ| 21:
Đ| 22:       case other of {{ Tensor:_ }} -> {
Đ| 23:         # mul to another Tensor
Đ| 24:         return Tensor(name= '('++ this.name ++ '*' ++ other.name ++')')
Đ| 25:       }
Đ| 26:
Đ| 27:       continue # as NotImplemented in Python
Đ| 28:     }
Đ| 29:
Đ| 30:     method (-) (other) case type(other) of {
Đ| 31:       # sub a constant
Đ| 32:       DecimalType -> Tensor(name= '('++ this.name ++ '-' ++ other ++')')
Đ| 33:
Đ| 34:       case other of {{ Tensor:_ }} -> {
Đ| 35:         # sub another Tensor
Đ| 36:         return Tensor(name= '('++ this.name ++ '-' ++ other.name ++')')
Đ| 37:       }
Đ| 38:
Đ| 39:       continue # as NotImplemented in Python
Đ| 40:     }
Đ| 41:
Đ| 42:     method (-@) (other) case type(other) of {
Đ| 43:       # sub from a constant
Đ| 44:       DecimalType -> Tensor(name= '('++ other ++ '-' ++ this.name ++')')
Đ| 45:
Đ| 46:       case other of {{ Tensor:_ }} -> {
Đ| 47:         error('not resolved to magic (-) of ' ++ lhv ++ ' ?!')
Đ| 48:       }
Đ| 49:
Đ| 50:       continue # as NotImplemented in Python
Đ| 51:     }
Đ| 52:
Đ| 53:     method (/) (other) case type(other) of {
Đ| 54:       # div by a constant
Đ| 55:       DecimalType -> Tensor(name= '('++ this.name ++ '/' ++ other ++')')
Đ| 56:
Đ| 57:       case other of {{ Tensor:_ }} -> {
Đ| 58:         # div by another Tensor
Đ| 59:         return Tensor(name= '('++ this.name ++ '/' ++ other.name ++')')
Đ| 60:       }
Đ| 61:
Đ| 62:       continue # as NotImplemented in Python
Đ| 63:     }
Đ| 64:
Đ| 65:     method (/@) (other) case type(other) of {
Đ| 66:       # div to a constant
Đ| 67:       DecimalType -> Tensor(name= '('++ other ++ '/' ++ this.name ++')')
Đ| 68:
Đ| 69:       case other of {{ Tensor:_ }} -> {
Đ| 70:         error('not resolved to magic (/) of ' ++ lhv ++ ' ?!')
Đ| 71:       }
Đ| 72:
Đ| 73:       continue # as NotImplemented in Python
Đ| 74:     }
Đ| 75:
Đ| 76:   }
Đ| 77:
Đ| 78: }
Tensor
Đ:
Đ: let (x, y) = (Tensor('x'), Tensor('y'))
Đ:
Đ: result = x + y; result?name
(x+y)
Đ: result = x + 5; result?name
(x+5)
Đ: result = 5 + x; result?name
(x+5)
Đ: result = x - 5; result?name
(x-5)
Đ: result = 5 - x; result?name
(5-x)
Đ: result = x * y; result?name
(x*y)
Đ: result = x / y; result?name
(x/y)
Đ: result = x * 3; result?name
(x*3)
Đ: result = 3 * x; result?name
(x*3)
Đ: result = x / 3; result?name
(x/3)
Đ: result = 3 / x; result?name
(3/x)
Đ:
Đ: result = 3 + x / 7 * (y - 5); result?name
(((x/7)*(y-5))+3)
Đ:
Đ: x + 'z'
* 😱 *
💔
📜 <interactive> 🔎 <adhoc>:1:1
📜 + 🔎 /home/cyue/Wander/e-wrks/edh/edh_modules/batteries/magic/arith.edh:2:23
📜 error 🔎 <host-code>
💣 Not possible to do (+) with ObjectType: <object: Tensor> and StringType: z
👉 /home/cyue/Wander/e-wrks/edh/edh_modules/batteries/magic/arith.edh:19:3
Đ:
```

## Reflections

Checkout [reflection.edh](./reflection.edh)

```bash
Đ: # expression is 1st class citizen in Edh
Đ:
Đ: # with original src reserved
Đ: x = expr a + b*c
a + b*c
Đ: type(x)
ExprType
Đ:
Đ: # without src info
Đ: x' = makeExpr( a + b*c )
<expr: InfixExpr "+" (AttrExpr (DirectRef (NamedAttr "a"))) (InfixExpr "*" (AttrExpr (DirectRef (NamedAttr "b"))) (AttrExpr (DirectRef (NamedAttr "c"))))>
Đ: type(x')
ExprType
Đ:
Đ: # a scope can be captured anywhere within Edh code
Đ: this'modu'scope = scope()
<object: <scope>>
Đ:
Đ: # this will fail as `x` references attributes unavailable
Đ: this'modu'scope.eval( x )
* 😱 *
💔
💣 Not in scope: NamedAttr "a"
👉 <genesis>:1:1
Đ:
Đ: # `scope.put()` is used to update attributes reflectively
Đ: this'modu'scope.put( a=5, b=3 )
Đ: # of course Edh code can update attributes normally
Đ: c = 7
7
Đ:
Đ: # now it should happily eval
Đ: this'modu'scope.eval( x )
26
Đ:
Đ: # a reflective scope can only be captured and exposed
Đ: # by its owning procedure willingly, some more demos
Đ:
Đ: {
Đ|  1:   method f(n) {
Đ|  2:     method g(m) {
Đ|  3:       scope()
Đ|  4:     }
Đ|  5:     return (scope(), g(5))
Đ|  6:   }
Đ|  7: }
f
Đ: let (s1, s2) = (*f(3))
Đ:
Đ: s2.lexiLoc()
g ( m, ) @ <adhoc>:2:17
Đ:
Đ: s1.attrs()
{ "g":g, "n":3, }
Đ:
Đ: s2.attrs()
{ "m":5, }
Đ:
Đ: s2.eval( expr m/n )
5/3
Đ:
Đ: {
Đ|  1:   s2.eval( assign'result = (expr
Đ|  2:     t=n/m
Đ|  3:   ) )
Đ|  4: }
pkargs( assign'result=3/5, )
Đ:
Đ: s2.attrs()
{ "m":5, "t":3/5, }
Đ: s2.t
3/5
Đ:
```

## Terminology

### World

> While impure computer programs tend to change the world, you create ones for
> them to manipulate, but with potentials limited.

The _world_ is a **niche**, **sandbox** or similar concepts you can call it.
To develop a **Haskell** + **Edh** application is somewhat like **playing God**,
you define an **Edh** world with its physics in entirety - no more, no less,
just what you **say** (_\*_), that ought to be there.

_\*_ not really enough to just say it,
[talk is cheap](https://lkml.org/lkml/2000/8/25/132)
, put the code there.

See this 190 lines of
[world modeling code](https://github.com/e-wrks/edhim#world-modeling-code-in-haskell)
for an example.

### Package

Checkout how [npm](https://www.npmjs.com/) manages
[NodeJS](https://nodejs.org/en/) packages to see the idea for better
dependency management that **Edh** follows.

Just a folder tree containing various `*.edh` file, resides directly or nested
some levels within the **Edh** interpreter's
[cwd](https://en.wikipedia.org/wiki/Working_directory)
or a `edh_modules` parent directory, so that reachable from `import` statements
from **Edh** code.

See [Package / Module Structures](#package--module-structures)

By far no meta data format has been defined for an **Edh** package, but there
ought to be one, together with a package tool managing version dependencies
as well as to auto download & install packages from some shared repositories.

### Module

Checkout how [npm](https://www.npmjs.com/) manages
[NodeJS](https://nodejs.org/en/) packages to see the idea for better
dependency management that **Edh** follows.

A **module** in **Edh** is a single `*.edh` file, imported by some **Edh**
code or **Haskell** code via the [EHI](#ehi-edh-host-interface).

See [Package / Module Structures](#package--module-structures)

Note that module `batteries/root` will be imported into root scope of an
**Edh** **world** when default batteries are installed (the most common case
when a **world** is created).

### Entity

An **entity** in **Edh** is the backing storage for a **scope**, with possibly an
**object** mounted to it with one **class** and many **supers**

> Well there actually can exist multiple **object**s mounted to one same entity,
> with different **class**es and/or set of **supers**, but that's the black magic
> you want to avoid.

#### Attribute

An entity stores **attribute**s associated with alphanumeric or symbolic keys.

#### Symbol

**Symbol** in **Edh** is much the same as
[Symbol in JavaScript](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Symbol)

A **symbol** can stand in place of an alphanumeric name, used to
address an attribute from an **object entity**, but symbols are
private to its owning scope, can not be imported from out side
of the scope, thus serves encapsulation purpose in object
structure designs.

And symbol values reside in a lexical outer scope are available
to its lexical inner scopes, e.g. a **symbol** bound to a **module** is
available to all **procedure**s defined in the **module**, and a **symbol**
bound within a **class procedure** is available to all its **method**s
as well as nested **class**es.

### Scope

Especially note that **Edh** has no block **scope** as in **C**
family languages, **JavaScript** neither does before **ES6**,
**Python** neither does until now (2020).

There is only **procedure scope** in **Edh**, see [Procedure](#procedure).

Every non-host **procedure** call will create a new **scope**, with
a new [entity](#entity) created for it, that:

- if it is a **constructor procedure** call, a new **object** of the
  called **class**, or the `<module>` class defined by the world,
  is allocated mounting the **entity**, serving `this` object of the
  **scope**;

- if it is a **methd procedure** call, no new **object** is created,
  and the **scope** inherits `this` **object** from the lexical outer
  **scope**, and the original **object** from which the **method**
  was obtained, becomes `that` **object** in this **scope**. `that`
  either contains the **method** in its **entity** as an **attribute**,
  or inherits the **method** from one of its **supers**.

### No Variable

Despite the existence of
[IORef](https://hackage.haskell.org/package/base/docs/Data-IORef.html),
[STRef](https://hackage.haskell.org/package/base/docs/Data-STRef.html),
[MVar](https://hackage.haskell.org/package/base/docs/Control-Concurrent-MVar.html)
and the very
[TVar](https://hackage.haskell.org/package/stm/docs/Control-Concurrent-STM-TVar.html)
and friends, the
[word "variable" as applied to **Haskell** variables](https://wiki.haskell.org/Variable)
is quite misleading.

**Edh** tries to get rid of it completely, by making **variable** a nonconcept.
But given the strong _imperative_ stylish of **Edh** code, **entity** **attribute**s
(see [Attribute](#attribute)) are likely to be misperceived as _variables_ in
traditional sense of imperative programming languages.

> I urge you to quarantine the _variable_ concept in context of a programming
> language and programming in general (it's still safe and sound in mathematics,
> statistics etc. of course), because that's how current generation of computing
> hardwares work, not how computing works in general.
>
> I still remember the hard time to wrap my head around `x = x + 1` when I was
> young and learning [BASIC](https://wiki.c2.com/?BasicLanguage) in enlightenment
> to programming (in fact to computer at all, on a
> [80286 computer](https://en.wikipedia.org/wiki/IBM_Personal_Computer_XT#IBM_XT_286)),
> the pleasure when I finally established the perception.
>
> But I'm not happy and feel false faith with that now.
>
> Using _variables_ in thoughts is anti-human, imagine yourself allocating a
> box area on a piece of paper, along with other tasks performed, you write sth
> into the box, erase it later followed by writing sth new, and repeat and repeat
> ... I would feel ridiculous. Computers ought to do that on their own, without
> the aid from human programmers.

At least, you should really convert your intuition when coding in **Edh**, for the
sake of the fact that you are programming transactional concurrency in contrast
to traditional single-threaded programs, or multi-threaded programs synchronized.

#### Attribute Assignment

Assignments in **Edh** may look like exactly as to change the value of a variable,
but actually, it is modification to the owning **entity** of the target
**attribute**.

Without an addressing prefix (`xxx.attr`), assigning to a named attribute
(`attr = expr`) is to update the **entity** of the nearest lexical **scope**,
associating with `attr` as the key, to evaluated value from the
_right-hand-side_ expr.

See [Object / Class](#object--class) for the concept of an **object**.

With an addressing prefix (`xxx.attr = expr`), `xxx` must evaluate to a value of
**object** type, assigning to a named attribute (`xxx.attr = expr`) or symbolic
attribute (`xxx.@sym = expr`), is to update the **entity** underlying the
**object** specified by the prefix, associating with `attr` or `@sym` as the key,
to evluated value from the _right-hand-side_ expr.

#### Attribute Read

Similar to the assignment, when `attr` `xxx.attr` and `xxx.@sym` appear in an
expression to be evaluated, those are not _variable_ reads as it looks like,
but actually reads of their respective owning **entities**.

#### Transactional Semantics Amplification

As said above, the read / write of attributes are semantically amplified to
their owning **entities**, to perceive this sense intuitively is crucial in
writing effective **Edh** code, or working **Edh** code at all. Because there
will definitely be chances you must delimit transaction boundaries for some
sections of your **Edh** code, see the [ai keyword](#the-ai-keyword), doing
that improperly or plainly wrong, you will be punished with excessive **stm**
retries or even dropped into infinite vain loops without progress.

Above said may sound pretty dreadful, but it should make you feel better if I
tell you that:

> When coding within an **Edh** world, you can forget about all kinds of
> [synchronization primitives](http://www.cs.columbia.edu/~hgs/os/sync.html)
> scattered
> [here](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/pthread.h.html),
> [here](https://golang.org/pkg/sync),
> and many _otherwheres_ , with every methods you attempt to program concurrency
> otherwise.
>
> Despite of many **async** frameworks trying to mitigate that disputable
> complexity, e.g.
> [async in JavaScript](https://caolan.github.io/async),
> [asyncio in Python](https://docs.python.org/3/library/asyncio.html),
> and [async in Haskell](http://hackage.haskell.org/package/async).

Checkout the implementation of
[concur](../edh_modules/batteries/root/concur.edh)
and [concur.edh in the Tour using that](./concur.edh).

`concur()` is just an example, it's straight forward for you to write application
logics in similar ways.

### Transaction (STM)

> EAFP in **Python** spirit:
>
> > Easier to ask for forgiveness than permission. This common Python coding
> > style assumes the existence of valid keys or attributes and catches
> > exceptions if the assumption proves false. This clean and fast style is
> > characterized by the presence of many try and except statements.
> > The technique contrasts with the LBYL style common to many other
> > languages such as C.

Well with
[Software transactional memory](https://en.wikipedia.org/wiki/Software_transactional_memory)
, you don't even ask for either forgiveness or permission, just do
what seems right to do, and it's done (with
[CAVEATs](#transactional-semantics-amplification)
though). It's called
[Optimistic Locking](http://en.wikipedia.org/wiki/Optimistic_locking)
elsewhere but the spirit is an upgraded version of **EAFP**.

In **Edh**, you get an implicit transaction in each of the following cases:

- Attribute assignment

```python
x = y + z
x += y # desugared to x = x+y
```

- Let assignment

```python
let (a.balance, b.balance) = (a.balance + amount, b.balance - amount)
```

- Arguments packing for a procedure call

  including explicit `pkargs(*,**,***)` call to construct an `ArgsPack`,
  which is to be yielded from a generator, published to an event sink etc.

```python
processItemsOfInterest ( *a.cart, *a.wishlist )
```

- pair / tuple / list / dict construction

  while multi-dimensional index construction (`a[x+o, y-3, z*5]`) is a
  special case of tuple construction

```haskell
case (x.pendingItems : x.doneItems) of {( p : d )} -> "Dash:\n"
  ++ join(p, sep='\n') ++ " --- \n" ++ join(d, sep='\n')
```

So above cases are intrinsically _atomic_, while for other cases that
atomicity / isolation are needed, you use:

#### The ai keyword

`ai` stands for **Atomically Isolatedly**, or `AtoIso` for short, it is used
as the transaction boundary delimiter.

`ai <expr>` is a statement where the expr (being a block is common case) is
guaranteed to be evaluated in a same transaction.

As based on [stm](http://hackage.haskell.org/package/stm), **Edh** will
atomically retry the whole transaction if inconsistency found before the tx
can commit successfully. And **Edh** will
[trace](https://hackage.haskell.org/package/base/docs/Debug-Trace.html#v:trace)
out the retries so end users will be aware of them.

Nested **ai** (block) expressions are technically doable, but should be
considered bad smell in the code under common circumstances.

### Function (or lack thereof)

To stay conceptually clear for the object system (which is
[procedural](https://en.wikipedia.org/wiki/Procedural_programming)
per se) living together with the
[functional](https://en.wikipedia.org/wiki/Functional_programming)
parts in the host language (i.e. **Haskell**), there are only **procedures**
but no **function** in **Edh** the surface language.

Simply put, in **Edh** terminology, a **procedure** tends to _change the world_,
while a **function** must stay
[side effect](<https://en.wikipedia.org/wiki/Side_effect_(computer_science)>)
free (well, there's no such a thing qualifies within an **Edh** world).

### Operator

**Edh** allows **operator** declaration and override similar to how **Haskell**
allows you. You can even roll your own, arbitrary new operators with a
precendence you'd like with.

Checkout the implementation of the default batteries of **Edh**:
[parts written in **Haskell**](../edh/src/Language/Edh/Batteries/)
and
[parts written in **Edh**](../edh_modules/batteries/)

You should be supprised that the following language constructs are all
implemented as overridable **operator**s in **Edh**:

- branch
  - (`->`)
- arrows
  - (`=>`), (`=>*`)
- assignment
  - (`=`), (`+=`), (`-=`), (`*=`), (`/=`)
- logical arithmetic
  - (`&&`), (`||`)
- list/dict/tuple comprehension/concatenation
  - (`=<`)
- list prepend / dict insert/update
  - (`=>`)
- string coercing concatenation
  - (`++`)
- event publish
  - (`<-`)

Meaning you can override them for the entire **Edh** world, or part of the
program **scope** (e.g. a **module**, a **class**).

Also see [**operator** procedure] below.

> Note that all are _left-associative_ _infix_ operators in **Edh**, except
> a few hardcoded _prefix_ operators:

- (`+`) prefix plus
- (`-`) prefix minus
- (`not`) prefix bool negation
- (`|`) guard

### Procedure

There are 3 kinds of procedures in **Edh**:

- [Host Procedure](#host-procedure)
- [Constructor Procedure](#constructor-procedure)
- [Method Procedure](#method-procedure)

#### Host Procedure

Host procedures are written in the host language (i.e. **Haskell**), and do
not create new **scope**s when called, including:

##### Vanilla Host Procedure

e.g.

```haskell
-- | utility null(*args,**kwargs) - null tester
isNullProc :: EdhProcedure
isNullProc !argsSender !exit = do
  !pgs <- ask
  packEdhArgs argsSender $ \(ArgsPack !args !kwargs) -> if null kwargs
    then case args of
      [v] -> contEdhSTM $ do
        isNull <- EdhBool <$> edhValueNull v
        exitEdhSTM pgs exit isNull
      _ -> contEdhSTM $ do
        argsNulls <- sequence $ ((EdhBool <$>) . edhValueNull) <$> args
        exitEdhSTM pgs exit (EdhTuple argsNulls)
    else contEdhSTM $ do
      argsNulls   <- sequence $ ((EdhBool <$>) . edhValueNull) <$> args
      kwargsNulls <- sequence $ Map.map ((EdhBool <$>) . edhValueNull) kwargs
      exitEdhSTM pgs exit (EdhArgsPack $ ArgsPack argsNulls kwargsNulls)
```

##### Host Operator Procedure

e.g.

```haskell
-- | operator (:) - pair constructor
consProc :: EdhProcedure
consProc [SendPosArg !lhExpr, SendPosArg !rhExpr] !exit = do
  pgs <- ask
  -- make sure left hand and right hand values are evaluated in same tx
  local (const pgs { edh'in'tx = True })
    $ evalExpr lhExpr
    $ \(OriginalValue !lhVal _ _) ->
        evalExpr rhExpr $ \(OriginalValue !rhVal _ _) ->
          contEdhSTM $ exitEdhSTM pgs exit (EdhPair lhVal rhVal)
consProc !argsSender _ =
  throwEdh EvalError $ "Unexpected operator args: " <> T.pack (show argsSender)
```

##### Host Generator Procedure

e.g.

```haskell
timelyNotify :: Int -> EdhGenrCaller -> STM ()
timelyNotify !delayMicros genr'caller@(!pgs', !iter'cb) = do
  nanos <- (toNanoSecs <$>) $ unsafeIOToSTM $ do
    threadDelay delayMicros
    getTime Realtime
  -- yield the nanosecond timestamp to iterator
  runEdhProc pgs' $ iter'cb (EdhDecimal $ fromInteger nanos) $ \_ ->
    timelyNotify delayMicros genr'caller

-- | host generator console.everyMicros(n) - with fixed interval
rtEveryMicrosProc :: EdhProcedure
rtEveryMicrosProc !argsSender _ = ask >>= \pgs ->
  case generatorCaller $ edh'context pgs of
    Nothing          -> throwEdh EvalError "Can only be called as generator"
    Just genr'caller -> case argsSender of
      [SendPosArg !nExpr] -> evalExpr nExpr $ \(OriginalValue nVal _ _) ->
        case nVal of
          (EdhDecimal (Decimal d e n)) | d == 1 ->
            contEdhSTM $ timelyNotify (fromIntegral n * 10 ^ e) genr'caller
          _ -> throwEdh EvalError $ "Invalid argument: " <> T.pack (show nVal)
      _ ->
        throwEdh EvalError $ "Invalid argument: " <> T.pack (show argsSender)
```

#### Constructor Procedure

Including:

##### Class Procedure

Runs with a new object as both `this` and `that`

Defined by a `class`statement in **Edh** code

##### Module Procedure

Runs with the new module object as both `this` and `that`

Defined by a `*.edh` file which is imported by **Edh** code

#### Method Procedure

Runs with _lexical_ `this` and _inheriting descendant_ `that`, including:

##### Vanilla Method Procedure

Defined by a `method` statement in **Edh**,
which is a vanilla callable after an alphanumeric name

##### Operator Procedure

Defined by an `operator` statement in **Edh**,
which is a **binary** or **trinary** callable after a name with just operator symbols
i.e. `=~!@#$%^&|:<>?+-*/` plus other
[Unicode](http://www.unicode.org/reports/tr44/tr44-14.html#GC_Values_Table)
[Symbols](https://hackage.haskell.org/package/base/docs/Data-Char.html#v:isSymbol)
.

The **binary** form receives `left'hand'value` and `right'hand'value` as arguments

The **trinary** form receives `callerScope`, `left'hand'expr` and `right'hand'expr`
as arguments

##### Generator Procedure

Defined by a `generator` statement in **Edh**,
which is only callable by a `for-from-do` loop, and contains `yield` expressions

##### Interpreter Procedure

Defined by an `interpreter` statement in **Edh**,
which is same as a vanilla **method** procedure except it receives arguments in
reflective expr forms rather than evaluated values, in addition to the reflective
`callerScope` as first argument

##### Producer Procedure

Defined by an `producer` statement in **Edh**, being a start point of event
producing via an [Event Sink](#event-sink), while its caller is the start
point of event consuming via the same event **sink**.

A **producer** procedure must take an `outlet` argument, which is the very
event **sink**. Whatever a **producer** procedure returns is just ignored,
the caller (event consumer) of a **producer** procedure will immediately
receive the same event **sink** as passed to the **producer** as its `outlet`
argument, while the **producer** procedure won't be actually executed until
the caller subscribed to that event **sink**. This way no event produced
after the **producer** procedure started will be missed by the caller
(event consumer).

### Go Routine

Checkout [Goroutine](https://tour.golang.org/concurrency) as in
[Go](https://golang.org/), if not already.

A **go** _routine_ in **Edh** is very similar to **goroutine**:

#### The go keyword

`go <expr>` is a statement in **Edh** for the specified computation be scheduled
to run in a separate _lightweigth-thread_ , while in case a forked thread throws
an exception, the execption will be
[throwTo](https://hackage.haskell.org/package/base/docs/Control-Concurrent.html#v:throwTo)
the main thread of the **Edh** program.

The sames as in **Go**:

- Things are prepared before you **go**

  i.e. callee procedure arguments are packed, `case-of` target is evaluated,
  `for-from-do` loop iterable is constructed, all in a transaction run by the
  current thread

- There is no _return_

  Once you **go**, you are not _awaited_ or _joined_ anyway

Yet there are differences:

- **Edh** can not only **go** a procedure call:

  You can **go** a **for-from-do** loop, a block, or even a single expression
  e.g. a `if-then` or a `case-of`

- Whenever not **go** calling another procedure:

  The lexical **scope** is shared among all threads forked from the originating
  thread, this is quite the opposite to
  [Share Memory By Communicating](https://blog.golang.org/share-memory-by-communicating)
  in **Go** spirit.

  Well in **Edh** you'd better neither do the **Go** anti-pattern described as

  > communicate by sharing memory

  While it's quite okay to read / modify the shared **scope** if it seems right,
  but for communication purpose, you use one or more [Event Sink](#event-sink)s,
  this is quite the same in **Go** spirit as communicating through
  [channels](https://tour.golang.org/concurrency/2) in **Go**.

  Guess what, you have even the same operator (**<-**) on **event sink**s in
  **Edh** as the **channel** operator in **Go**. But just remember a **Go**
  **channel** does _unicast_ while an **Edh** **sink** does _broadcast_ .

#### The defer keyword

See [Break the thread from reactor](#break-the-thread-from-reactor),
as **Edh** threads can be terminated by `break`s from **reactor**s,
even exception handlers on the thread can cease to run on such terminations.

You use **defer** to do necessary cleanups or to schedule other computations
to run upon thread termination.

`defer <expr>` is a statement in **Edh** for the specified computation be
scheduled to run upon current thread's termination.

Similar to [defer](https://golang.org/ref/spec#Defer_statements) in
**Go**:

- Input to the execution is prepared at scheduling time

  i.e. callee procedure arguments are packed, `case-of` target is evaluated,
  `for-from-do` loop iterable is constructed, all in a transaction run
  immediately by the current thread on encounter of the **defer** statement

- Multiple **defer**s are run in _last-in-first-out_ order upon thread
  termination

Differences with [defer](https://golang.org/ref/spec#Defer_statements) in
**Go**:

- A **defer**ed computation runs upon thread termination in **Edh** while in
  **Go** a **defer**ed function call runs on return of the surrounding
  function

- **Edh** can not only **defer** a procedure call:

  You can **defer** a **for-from-do** loop, a block, or even a single
  expression e.g. a `if-then` or a `case-of`

- Whenever not **defer** calling another procedure:

  The lexical **scope** is shared among the originating thread and other
  **defer**ed computations

### Event Sink

An **event sink** is a value of special type in **Edh**, a new **sink** is
created each time the `sink` keyword is evaluated in **Edh**, as the name
implies, events from everywhere can flow into a **sink**, a **Go** **channel**
can have multiple writers so they are similar in this respect.

But write to a **channel** will block when there is no reader (and the buffer
is full if writing to a buffered **channel**), while write to a **sink**
will always success immediately, the written event is silently dropped when
there is no reader draining the sink.

And when there are multiple readers, a **channel** gives one **msg** to a
unique reader only (i.e. load balancing semantics), while a **sink** gives
the same **event** to all readers (i.e. broadcasting semantics).

#### The reactor Procedure

A **reactor** is defined by a `reactor` statement in **Edh** code, specifying
the **sink** to be associated with, a procedure body consists of **Edh** code,
and an **arguments receiver** to receive the event value into the procedure
body's **scope** before running.

Draining of events from each's respective event **sink** by **reactor**s
attached to a thread, have higher priority than normal tx jobs on the thread,
in common cases, event streams won't appear like a tight-loop, so **reactors**
will appear to run **interleaved** with normal transactions on the thread.

But the next normal tx job won't get executed unless all **reactor**s stay
un-fired, meaning their respective event **sink**s are all in silence for
that instant in time.

Fairness in processing of tight-loop-like event streams needs to be further
explored sooner than later.

#### Break the thread from reactor

Another special mechanism with **reactor** is that it can conditionally
evaluate to a `<break>` result (by a `break` statement in it's body), in
which case the thread having it attached will be terminated.

### Value / Type

> Everything in **Edh** is a value

Code may tell better here:

```haskell
-- | everything in Edh is a value
data EdhValue =
  -- | type itself is a kind of (immutable) value
      EdhType !EdhTypeValue
  -- | end values (immutable)
    | EdhNil
    | EdhDecimal !Decimal
    | EdhBool !Bool
    | EdhString !Text
    | EdhSymbol !Symbol

  -- | direct pointer (to entities) values
    | EdhObject !Object

  -- | mutable containers
    | EdhDict !Dict
    | EdhList !List

  -- | immutable containers
  --   the elements may still pointer to mutable data
    | EdhPair !EdhValue !EdhValue
    | EdhTuple ![EdhValue]
    | EdhArgsPack ArgsPack

  -- executable precedures
    | EdhIntrOp !Precedence !IntrinOpDefi
    | EdhClass !ProcDefi
    | EdhMethod !ProcDefi
    | EdhOprtor !Precedence !(Maybe EdhValue) !ProcDefi
    | EdhGnrtor !ProcDefi
    | EdhIntrpr !ProcDefi
    | EdhPrducr !ProcDefi

  -- | flow control
    | EdhBreak
    | EdhContinue
    | EdhCaseClose !EdhValue
    | EdhFallthrough
    | EdhYield !EdhValue
    | EdhReturn !EdhValue

  -- | event sink
    | EdhSink !EventSink

  -- | named value
    | EdhNamedValue !AttrName !EdhValue

  -- | reflective expr, with source (or not, if empty)
    | EdhExpr !Unique !Expr !Text

edhValueNull :: EdhValue -> STM Bool
edhValueNull EdhNil                  = return True
edhValueNull (EdhDecimal d         ) = return $ D.decimalIsNaN d || d == 0
edhValueNull (EdhBool    b         ) = return $ not b
edhValueNull (EdhString  s         ) = return $ T.null s
edhValueNull (EdhSymbol  _         ) = return False
edhValueNull (EdhDict    (Dict _ d)) = Map.null <$> readTVar d
edhValueNull (EdhList    (List _ l)) = null <$> readTVar l
edhValueNull (EdhTuple   l         ) = return $ null l
edhValueNull (EdhArgsPack (ArgsPack args kwargs)) =
  return $ null args && odNull kwargs
edhValueNull (EdhExpr _ (LitExpr NilLiteral) _) = return True
edhValueNull (EdhExpr _ (LitExpr (DecLiteral d)) _) =
  return $ D.decimalIsNaN d || d == 0
edhValueNull (EdhExpr _ (LitExpr (BoolLiteral b)) _) = return b
edhValueNull (EdhExpr _ (LitExpr (StringLiteral s)) _) = return $ T.null s
edhValueNull (EdhNamedValue _ v) = edhValueNull v
edhValueNull _ = return False
```

```haskell
edhUltimate :: EdhValue -> EdhValue
edhUltimate (EdhNamedValue _ v) = edhUltimate v
edhUltimate v                   = v

edhExpr :: Expr -> STM EdhValue
edhExpr (ExprWithSrc !xpr !xprSrc) = do
  u <- unsafeIOToSTM newUnique
  return $ EdhExpr u xpr xprSrc
edhExpr x = do
  u <- unsafeIOToSTM newUnique
  return $ EdhExpr u x ""

nil :: EdhValue
nil = EdhNil

-- | Resembles `None` as in Python
--
-- assigning to `nil` in Edh is roughly the same of `delete` as
-- in JavaScript, and `del` as in Python. Assigning to `None`
-- will keep the dict entry or object attribute while still
-- carrying a semantic of *absence*.
edhNone :: EdhValue
edhNone = EdhNamedValue "None" EdhNil

-- | Similar to `None`
--
-- though we don't have `Maybe` monad in Edh, having a `Nothing`
-- carrying null semantic may be useful in some cases.
edhNothing :: EdhValue
edhNothing = EdhNamedValue "Nothing" EdhNil

-- | With `nil` converted to `None` so the result will never be `nil`.
--
-- As `nil` carries *delete* semantic in assignment, in some cases it's better
-- avoided.
noneNil :: EdhValue -> EdhValue
noneNil EdhNil = edhNone
noneNil !v     = v

nan :: EdhValue
nan = EdhDecimal D.nan

inf :: EdhValue
inf = EdhDecimal D.inf

true :: EdhValue
true = EdhBool True

false :: EdhValue
false = EdhBool False
```

### Object / Class

A **class** in **Edh** is defined by a `class` statement in **Edh**
code in form of a **class** procedure.

A **class** procedure constructs **object**s when called, on each
invocation, it implicitly creates an **object** taking the **class**
and _many_ (reads zero-to-multiple) **supers** (declared by _many_
`extends` statements within the **class** procedure) mounted on the
**scope** **entity** of the **class** procedure call.

> A **class** procedure can explicitly return another **object**, another
> **value** or even `nil`, but again, this is the black magic you want to
> avoid.

A **class** procedure can take no argument, to receive arguments for
object construction, a `__init__()` method should be defined within the
**class** procedure, then construction arguments are passed to it
automatically.

Note in traditional **Object Oriented** languages, the **class** is
sensibly a part of the definition of the world structure, which carries
rather _static_ semantics, **Python** had made the **class** more
dynamic in constitutional respects, but seemed most people have ignored
that and continued to model the program's world with statically sensing
classes.

The **class** descends to be just a (well still 1st class) citizen in
an **Edh** world, it's conventionally serving _attribute grouping_
purpose for the majority cases, i.e. an **object** should be sensed as
a _namespace_ for **attribute**s otherwise not possible to stay together
except being members of a same, single **object**'s underlying
**entity**.

#### This reference

`this` refers to the nearest context **object** in lexical scope hierarchy.

#### That reference

`that` refers to the **object** against which current running
**procedure** is resolved, i.e. the target **object** of attribute
resolution in finding the current (**method**) **procedure** as a callee.

`that` either contains the **method** procedure in its own **entity** as
an **attribute**, in which case `that` should be the same as `this`,
or `that` inherits the **method** from one of its **supers**, which is,
`this`.

It makes sense to remember that `this` **object** was (or is being)
constructed by the nearest lexical **class** **procedure**, while `that`
**object** was not.

#### Super

During the run of a **class** procedure, each `extends` statement adds
its specified **object** as a **super** object of `this` object under
construction.

> Well a **method** procedure can contain `extends` statements too and
> when called will add **super**(s) possibly after its `this` **object**
> has been constructed. Still this is the black magic you want to avoid.

Last **super** added is the first attempted target in attribute resolution
against `this` object, if no attribute associated with the interesting key
directly presents in `this` object's underlying **entity**.

### EHI (Edh Host Interface)

With **Haskell** as the host language, **Edh** as the surface language,
the **EHI** defines the interface for host code in **Haskell** to create
& control embedded **Edh** worlds, and to splice host (typically
side-effects free, i.e. pure, and fast-in-machine-speed)
functions, wrapped as host procedures, with procedures written
in **Edh**, those do arbitrary manipulations on arbitrary objects
in the world, but, less speedy as with interpreted execution.
