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

* Added new definitions to `Algebra.Bundles`:
  ```agda
  record UnitalMagma c ℓ : Set (suc (c ⊔ ℓ))
  record Quasigroup  c ℓ : Set (suc (c ⊔ ℓ))
  ```
  and the existing record `Lattice` now provides
  ```agda
  ∨-commutativeSemigroup : CommutativeSemigroup c ℓ
  ∧-commutativeSemigroup : CommutativeSemigroup c ℓ
  ```
  and their corresponding algebraic subbundles.

* Added new definitions to `Algebra.Structures`:
  ```agda
  record IsUnitalMagma (_∙_ : Op₂ A) (ε : A) : Set (a ⊔ ℓ)
  record IsQuasigroup  (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ)
  ```
  and the existing record `IsLattice` now provides
  ```
  ∨-isCommutativeSemigroup : IsCommutativeSemigroup ∨
  ∧-isCommutativeSemigroup : IsCommutativeSemigroup ∧
  ```
  and their corresponding algebraic substructures.
