# Enclose entities, not variables

Closures in conventional programming languages enclose variables separately,
that's not the case with **Đ (Edh)**.

**Đ (Edh)** scopes are backed by entities, each entity has its own dynamic set
of attributes, updated at runtime. An **Đ (Edh)** procedure encloses all of its
lexical scopes.

An assigning operation with the target not **dot-notation** designated, is
interpreted to be targeting current scope, i.e. to create, update or delete (in
case the value to be assigned is `nil`) the attribute by the specified key,
on the entity backing current scope.

This means it is not possible for a statement/expression to change some
attribute resides in any of its lexical outer scopes, contrary to what
conventional closure semantics permit.

**Đ (Edh)** provides the `namespace` construct to support such objectives. A
namespace is a special object created ad-hoc with its attribute key specified
as part of the syntax, the attribute key can then be used as the leading part
of the **dot-notation** as an assignment target, from within any inner scopes
to create / update / delete attributes on the namespace object.

Combined with the transactional nature of **Đ (Edh)**, though you can think of
an **Đ (Edh)** attribute similar to a conventional variable, you should keep its transactional semantics in mind too, i.e. adding/deleting other attributes
to/from its owing entity will render reading and writting of the attribute
inconsistent per the **STM** transaction pending commit, thus retrie(s). Whereas
it's technically implemented, when no attribute is added/deleted to/from its
owning entity concurrently to the reading/writing of an attribute, **STM** will
only isolate concurrent readings/writings of the very attribute, regardless of
readings/writings of other attributes on the same entity.

This design of **Đ (Edh)** is to favor dynamic evaluation of expressions
anytime anywhere, by preserving the full context. But it leads to a CAVEAT,
that it's much easier to leak resources bound to any scope in the hierarchy of
the lexical context where a procedure is defined, in case you return the
procedure as a 1st class value, for it to be retained elsewhere for a long time.

You are adviced to more aggressively clear references to resource values once
not needed anymore, as the closure machinery is not doing this automatically for
you.
