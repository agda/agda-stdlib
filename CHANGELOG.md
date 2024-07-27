Version 2.2-dev
===============

The library has been tested using Agda 2.6.4.3.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Solver.CommutativeMonoid`:
  ```agda
  normalise-correct  ↦  Algebra.Solver.CommutativeMonoid.Normal.correct
  ```

* In `Algebra.Solver.IdempotentCommutativeMonoid`:
  ```agda
  flip12             ↦  Algebra.Properties.CommutativeSemigroup.xy∙z≈y∙xz
  normalise-correct  ↦  Algebra.Solver.IdempotentCommutativeMonoid.Normal.correct
  ```

* In `Algebra.Solver.Monoid`:
  ```agda
  homomorphic        ↦  Algebra.Solver.Monoid.Normal.comp-correct
  normalise-correct  ↦  Algebra.Solver.Monoid.Normal.correct
  ```

New modules
-----------

* Refactoring of the `Algebra.Solver.*Monoid` implementations, via
  a single `Tactic` module API based on the existing `Expr`, and
  a common `Normal`-form API:
  ```agda
  Algebra.Solver.CommutativeMonoid.Normal
  Algebra.Solver.IdempotentCommutativeMonoid.Normal
  Algebra.Solver.Monoid.Expression
  Algebra.Solver.Monoid.Normal
  Algebra.Solver.Monoid.Tactic
  ```

Additions to existing modules
-----------------------------

* In `Algebra.Solver.Ring`
  ```agda
  Env : ℕ → Set _
  Env = Vec Carrier
  ```
