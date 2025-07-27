Version 2.4-dev
===============

The library has been tested using Agda 2.8.0.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

* The type of `Relation.Nullary.Negation.Core.contradiction-irr` has been further
  weakened so that the negated hypothesis `¬ A` is marked as irrelevant. This is
  safe to do, in view of `Relation.Nullary.Recomputable.Properties.¬-recompute`.

* As a consequence, the type of `Data.Fin.Base.lower₁` has been correspondingly
  weakened so that the negated hypothesis `n≢i : n ≢ toℕ i` is marked irrelevant.

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

Additions to existing modules
-----------------------------
