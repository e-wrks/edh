# Đ (Edh) - The next-big-things ought to happen with Haskell not C/C++

[![Gitter](https://badges.gitter.im/e-wrks/community.svg)](https://gitter.im/e-wrks/community?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)

**Quick Start**

- Take [A Tour of Đ (Edh)](./Tour/)
- Checkout the demo & scaffold project:
  [EdhIm - Đ (Edh) doing Instant Messaging](https://github.com/e-wrks/edhim)

> **Đ (Edh)** code should be especially more _readable_/_modifiable_
> to average people without a
> [functional](#functional---try-not-to-abuse-this-concept)
> mindset (yet), thus development of a software project in **Haskell** + **Edh**
> can be more viable and maintainable by teams with diversified crew members.
>
> One possible division of labour on from the scaffold as a baseline, e.g.
>
> - Junior people and New Comers (the Dev), End Users (bugfixers):
>
>   Extend [Đ (Edh) code](https://github.com/e-wrks/edhim/Readme.md#full-%c4%90-edh-code-95-loc) with new modules,
>   3rd party packages for application / business logics, with fast
>   iterations
>
> - Thinkist people:
>
>   Establish the
>   [world modeling code](https://github.com/e-wrks/edhim/Readme.md#world-modeling-code-in-haskell-190-loc),
>   then progressively (but may better conservatively) improve the models,
>   for mistakes harder to be made, idiomatics easier to be followed
>
> - Architect / Senior Engineering people, Security Experts, the Ops:
>
>   Establish and maintain
>   [world reifying code](https://github.com/e-wrks/edhim/Readme.md#world-reifying-code-in-haskell-193-loc),
>   ensure the systems run continuously & securely on a foundation of
>   contemporary technology stack, deal with dependency EOLs, patch CVEs in
>   time, perform regularly the house keeping of backing storage

- [What is Đ (Edh)](#what-is-đ-edh)
  - [Program Concurrency and Data Consistency as a whole](#program-concurrency-and-data-consistency-as-a-whole)
  - [The Mission](#the-mission)
- [The name](#the-name)
- [Philosophy](#philosophy)
  - [About Everything](#about-everything)
  - [Object? - Yes, Oriented? - No](#object---yes-oriented---no)
  - [Functional? - Try not to abuse this concept](#functional---try-not-to-abuse-this-concept)
  - [Performance Goals](#performance-goals)
- [Zen of Đ (Edh)](#zen-of-đ-edh)
- [Licensing](#licensing)
- [Academic relationship](#academic-relationship)
- [A joke](#a-joke)

## What is Đ (Edh)

**Edh** is a **dynamically** & **strongly** typed, **procedural** (thus
**imperative**), **value-oriented** (i.e. **immutable** first, yet with
**non-traditional** **Object** constructs), **interpreted** programming
language, that **parasitic** on [GHC](https://haskell.org/ghc)
and heavily relying on
[the Haskell implementation](http://hackage.haskell.org/package/stm)
of
[Software Transactional Memory](https://en.wikipedia.org/wiki/Software_transactional_memory)
for unified intuition of **concurrency** and **data-consistency**.

**Edh** tries to bridge **procedural** mindsets to **functional** mindesets
as smooth as possible, by following good spirits, designs and practices of
**Python**, **Go**, **JavaScript**, while aiming at **Haskell** in
pursuit of quality in the software to be developed.

**Edh** implements its version of the `go` statement that
[not guilty](./GoNoGoto2.0.md) on the
[goto 2.0 charge](https://vorpus.org/blog/notes-on-structured-concurrency-or-go-statement-considered-harmful/#go-statement-considered-harmful)

### [Program Concurrency and Data Consistency as a whole](./Tour/Readme.md#programming-concurrency-and-data-consistency-as-a-whole)

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
[concur](./edh_modules/batteries/root/concur.edh)
and [concur.edh in the Tour using that](./Tour/concur.edh).

`concur()` is just an example, it's straight forward for you to write
application logics in similar ways.

### The Mission

**Edh** competes with [Python](https://python.org) in aid of **Haskell**
instead of **C**/**C++** to be the breeding ground for next phenomenal
pieces of software, after [TensorFlow](https://tensorflow.org),
[Pandas](https://pandas.pydata.org/), [Numpy](https://numpy.org/) etc.
by providing equaly good or even better language constructs to rivals
in **Python**.

Take the [Tour](./Tour/) to see what **Edh** has to offer.

[**Julia**](https://julialang.org) is an alternative all-in-one solution
for the **next-big-things**, but as well as **Haskell**, **Julia** carries
high impedance to average people without highly developed
[Mathematical Mindsets](https://www.aft.org/ae/winter2018-2019/boaler)

> But in the early years of school, we live in a system whereby students
> are required, from an early age, to learn many formal mathematical methods,
> such as those used to add, subtract, divide, and multiply numbers.
> This is the time when students stray from mathematical mindsets and develop
> fixed, procedural mindsets.

I suppose years still needed for our education system to get that situation
straight, and before that -

**Edh** is faithful to get people with just **Python**/**JavaScript**/**Go**
knowledge and skills started with a
[procedural](https://en.wikipedia.org/wiki/Procedural_programming)
[world](./Tour/Readme.md#world)
with [object](./Tour/Readme.md#object--class)s
in **Haskell** (and in **Julia** too I sincerely hope for chances).

## The name

**Edh** stands for **Event Distributing & Hosting**

Đ is a more stylish, single letter, symbolic name of **Edh** the language

## Philosophy

### About Everything

In **Edh**:

> Everything is a **value**,
> the **object** is a type of **value** among other (mostly immutable)
> types

This is part of the reason why **Edh** is not an _Object Oriented_
language (see next section), to be contrasted with **Python**, where:

> Everything is an **object**,
> a **value** is an **object** of some type among other types

### Object? - Yes, Oriented? - No

Many don't consider **Go** ([GoLang](https://golang.org)) an
_Object Oriented_ programming language, neither is **Edh** in similar
respect. **Edh** does pointer-wise
[Type Embedding](https://go101.org/article/type-embedding.html)
in **Go** spirit, while it takes a small step further to offer `that`
reference, which refers to a descendant record from an ancestor
method, in addition to `this` reference which refers to the lexical
self record.

### Functional? - Try not to abuse this concept

In a pure _functional_ language like **Haskell**, everything is a computation,
[Referencial Transparency](https://wiki.haskell.org/Referential_transparency)
is an intrinsic (and really fundamental) property. Bearing the world-changing
potential, a procedure in **Edh** can never qualify as a _function_.

But if you ask about
[Functional programming](https://www.geeksforgeeks.org/functional-programming-paradigm/)
as a possible paradigm you _DIY_, **Edh** is supportive as well as
other mainstream languages.

### Performance Goals

**Edh** struggles to dig performance improvements majorly out of the
_human_ aspect from the _human:machine_ pair, offer wider tolerance,
therefore better leverage, over diversified skill sets/levels among
all crew members onboard.

This is in the spirit of [Ruby](https://www.ruby-lang.org/en/about).
Though [Ruby](https://www.ruby-lang.org) took the road even more
_Object Oriented_, while **Edh** picked an alternative one, they are
both **Human Oriented**.

And raw machine performance squeezing is offloaded to
[GHC](https://wiki.haskell.org/GHC) who has been undescribable good
at it since inception.

## Zen of Đ (Edh)

- Always keep in mind that **Đ** the language and its ecosystem can become as
  horrible as **JavaScript** is, if overly used in wrong ways.

  Clues for the language as described
  [here](https://medium.com/javascript-non-grata/he-top-10-things-wrong-with-javascript-58f440d6b3d8)
  , some issues have been fixed in **Đ** while others remain pretty
  the same.

  And `edh_modules` has the potential to become bloated `node_modules` as well.

  So do programing, modeling and thinking in
  [**Haskell**](https://www.haskell.org)
  (i.e. be a _Haskeller_), as much as you can.

  For the ones who you must work with but hasn't feel comfortable with
  **Haskell**, ask him/her to use **Đ**, and write
  [host procedures](../Tour#host-procedures)
  wrapping idiomatic solutions in **Haskell** to help get his/her job done.

- Under certain circumstances, there are sweet spots balanced between
  _imperative_ and _declarative_ stylish, when put together, **Đ**
  code can be made even more concise than **Haskell** code (
  [see proof here](https://github.com/e-wrks/edhim#full-%C4%91-edh-code-95-loc)
  ). Do **Đ** programming around such sweet spots when you can find
  them, and when you do, be _Edhic_, that to be _Edhic_, is to be
  more _Pythonic_ than being
  [**Pythonic**](https://www.python.org/dev/peps/pep-0020).

- Whenever you're not sure how to get a bullshit job done, think about how a
  [**Gopher**](https://blog.golang.org/gopher) would do it

## Licensing

I (Compl Yue) choose to distribute **Edh** related code under BSD,
I believe BSD license is proper, it is even permissive for you
to re-license it under GPL etc. given the BSD clauses kept distributed
together. Though I sincerely hope no one is to attack me by patent
infringement.

## Academic relationship

No academic background relevant so far, but I (Compl Yue) do feel some
ideas here worth further exploration, to be consolidated or even
formalized on theoretical ground. If you are doing relevant CS
researches, **Edh** is yet another piece of friendly _BSD_ licensed
software at your hand, PRs updating information here, including
citation requests for your relevant work are welcomed.

## A joke

Finally let me tell you a joke:

> Q:
>
> > So what's good on **Edh** the programming language?
>
> A:
>
> > **Edh** is good because it's arguably a _three star_ language
> > (`***argspk`), as **Python** is arguably a _two star_ language
> > (`**kwargs`), while others are at most _one star_ languages or
> > even _no star_ ones.
