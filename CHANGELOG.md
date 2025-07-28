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

* Similarly type of `Data.Fin.Base.punchOut` has been weakened so that the negated
  equational hypothesis `i ≢ j` is marked as irrelevant. This simplifies some of
  the proofs of its properties, but also requires some slightly more explicit
  instantiation in a couple of places.

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

Additions to existing modules
-----------------------------
