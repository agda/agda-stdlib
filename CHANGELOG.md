Version 2.4-dev
===============

The library has been tested using Agda 2.8.0.

Highlights
----------

Bug-fixes
---------

* Fix a type error in `README.Data.Fin.Relation.Unary.Top` within the definition of `>-weakInduction`.

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

* The types of `Data.Vec.Base.{truncate|padRight}` have been weakened so
  that the argument of type `m ≤ n` is marked as irrelevant. This should be
  backwards compatible, but does change the equational behaviour of these
  functions to be more eager, because no longer blocking on pattern matching
  on that argument. Corresponding changes have been made to the types of their
  properties (and their proofs).

* Refactored usages of `+-∸-assoc 1` to `∸-suc` in:
  ```agda
  README.Data.Fin.Relation.Unary.Top
  Algebra.Properties.Semiring.Binomial
  Data.Fin.Subset.Properties
  Data.Nat.Binary.Subtraction
  Data.Nat.Combinatorics
  ```

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

Additions to existing modules
-----------------------------

* In `Data.Nat.Properties`:
  ```agda
  ∸-suc : m ≤ n → suc n ∸ m ≡ suc (n ∸ m)
  ```

