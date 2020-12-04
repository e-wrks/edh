# Enclose entities, not variables

Closures in conventional programming languages enclose **variable**s separately, that's not the case with **Đ (Edh)**.

First of all, _variable_ as most computer programming languages have defined it, is a misconception of mathematical **variable**, quoting https://existentialtype.wordpress.com/2013/07/22/there-is-such-a-thing-as-a-declarative-language

> ... The declarative concept of a variable is the mathematical concept of an unknown that is given meaning by substitution. The imperative concept of a variable, arising from low-level machine models, is instead given meaning by assignment (mutation), and, by a kind of a notational pun, allowed to appear in expressions in a way that resembles that of a proper variable. But the concepts are so fundamentally different, that I ([Robert Harper](https://existentialtype.wordpress.com/about)) argue in [PFPL](http://www.cambridge.org/us/academic/subjects/computer-science/programming-languages-and-applied-logic/practical-foundations-programming-languages) that the imperative concept be called an “assignable”, which is more descriptive, rather than “variable”, whose privileged status should be emphasized, not obscured.

> The problem with purely imperative programming languages is that they have only the concept of an assignable, and attempt to make it serve also as a concept of variable. The results are a miserable mess of semantic and practical complications. Decades of work has gone into rescuing us from the colossal mistake of identifying variables with assignables. ...

As a purposeful imperative language, **Đ (Edh)** tries to avoid such misconceptions, so we talk about **procedure**s instead of **function**s (as in **C** semantics), and **attribute**s of **entitie**s (complying to assignable semantics) instead of **variable**s.

There are 3 general types of scopes in **Đ (Edh)**:

- Object Scope, be of an object, which possibly being:
  - a namespace object
  - a vanilla object
- Procedure Scope, per each call against a procedure, which possibly being:
  - a class defining procedure
  - a namespace initializing procedure
  - a vanilla method procedure
  - a generator procedure
  - a producer procedure
  - an arrow procedure (vanilla/generator/producer)
- Module Scope, be of a module object, it is:
  - similar to a procedure scope when the module is being loaded, i.e. during execution of module source file
  - similar to an object scope after the module is loaded

All **Đ (Edh)** scopes are backed by **entitie**s, each **entity** has its own dynamic set of **attribute**s, updated at runtime. An **Đ (Edh)** procedure encloses all of its lexical scopes.

An assigning operation with the target not **dot-notation** designated, is interpreted to be targeting current scope, i.e. to create, update or delete (in case the value to be assigned is `nil`) the attribute by the specified key, on the entity backing current scope.

This means it is not possible for a statement/expression to change some attribute resides in any of its lexical outer scopes, contrary to what conventional closure semantics permit.

The `namespace` construct is provided to support such objectives. A namespace is a special object created ad-hoc with its attribute key specified as part of the syntax, the attribute key can then be used as the leading part of the **dot-notation** as an assignment target, from within any inner scopes to create / update / delete attributes on the namespace object.

Combined with the transactional nature of **Đ (Edh)**, though you can think of an **Đ (Edh)** **attribute** similar to a conventional (yet misconcepted) **variable**, you should keep its transactional semantics in mind too, whereas adding/deleting an attribute to/from its owing entity will render reading and writting of any other attribute of the entity inconsistent per the **STM** transaction pending commit, thus subject to retry. Whereas it's technically implemented, when no attribute is added/deleted to/from its owning entity concurrently to the reading/writing of an attribute, **STM** will only isolate concurrent readings/writings of the very attribute, regardless of readings/writings of other attributes on the same entity.

This design of **Đ (Edh)** is to favor dynamic evaluation of expressions anytime anywhere, by preserving the full context. But it leads to a CAVEAT:

- It's much easier to leak resources bound to any scope in the hierarchy of the lexical context where a procedure is defined, in case you return the procedure as a 1st class value, for it to be retained elsewhere for a long time.
- So you are adviced to more aggressively clear references to resource values once not needed anymore, as the closure machinery is not doing this automatically for you.
