Version 1.8-dev
===============

The library has been tested using Agda 2.6.2.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Deprecated modules
------------------

Deprecated names
----------------

New modules
-----------

* Identity morphisms and composition of morphisms between algebraic structures:
  ```
  Algebra.Morphism.Construct.Composition
  Algebra.Morphism.Construct.Identity
  ```

Other minor additions
---------------------

* In `Algebra.Bundles`, `Lattice` now provides
  ```agda
  ∨-commutativeSemigroup : CommutativeSemigroup c ℓ
  ∧-commutativeSemigroup : CommutativeSemigroup c ℓ
  ```
  and their corresponding algebraic subbundles.

* In `Algebra.Structures`, `IsLattice` now provides
  ```
  ∨-isCommutativeSemigroup : IsCommutativeSemigroup ∨
  ∧-isCommutativeSemigroup : IsCommutativeSemigroup ∧
  ```
  and their corresponding algebraic substructures.

Other minor additions
---------------------
