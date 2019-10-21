Library Design
==============

Documents library design decisions, big and small.

Smaller Design Decisions
------------------------

- `⊥` in `Data.Empty` and `⊤` in `Data.Unit` are not `Level`-polymorphic as that
  tends to lead to unsolved metas (see discussion at issue #312).  For that purpose,
  there are now level-polymorphic version in `Data.Empty.Polymorphic` and
  `Data.Unit.Polymorphic` respectively.
