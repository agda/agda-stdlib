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

New modules
-----------

* Properties of `IdempotentCommutativeMonoid`s refactored out from `Algebra.Solver.IdempotentCommutativeMonoid`:
  ```agda
  Algebra.Properties.IdempotentCommutativeMonoid
 ```

* Isomorphism between `Fin` and an 'obvious' definition `ℕ<` of
  'bounded natural number' type, in:
  ```agda
  Data.Nat.Bounded
  Data.Nat.Bounded.Base
  Data.Nat.Bounded.Literals
  Data.Nat.Bounded.Properties
 ```

Additions to existing modules
-----------------------------

* New lemma in `Data.Vec.Properties`:
  ```agda
  map-concat : map f (concat xss) ≡ concat (map (map f) xss)
  ```
