* Level polymorphism

`⊥` in `Data.Empty` and `⊤` in `Data.Unit` are not `Level`-polymorphic as that
tends to lead to unsolved metas (see discussion at issue #312).  This is understandable
as very often the level of (say) `⊤` is under-determined by its surrounding context,
leading to unsolved metas. This is frequent enough that it makes sense for the default
versions to be monomorphic (at Level 0).

But there are other cases where exactly the opposite is needed.  for that purpose,
there are level-polymorphic versions in `Data.Empty.Polymorphic` and
`Data.Unit.Polymorphic` respectively.

The same issue happens in `Relation.Unary` which defines `Ø` and `U` at `Level` 0, else
a lot of unsolved metas appear (for example in `Relation.Unary.Properties`). For that
purpose, `Relation.Unary.Polymorphic` exists.
