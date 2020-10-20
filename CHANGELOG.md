Version 1.5-dev
===============

The library has been tested using Agda 2.6.1 and 2.6.1.1.

Highlights
----------

Bug-fixes
---------

* The example module `Maybe` in `Relation.Binary.Construct.Closure.Reflexive` was accidentally exposed publicly. It has been made private.

* Fixed the type of the proof `map-id` in `List.Relation.Unary.All.Properties`, which was incorrectly abstracted over
  unused module parameters.

Non-backwards compatible changes
--------------------------------

* The internal build utilities package `lib.cabal` has been renamed
  `agda-stdlib-utils.cabal` to avoid potential conflict or confusion.
  Please note that the package is not intended for external use.

Deprecated modules
------------------

* The module `TransitiveClosure` in `Induction.WellFounded` has been deprecated. You should instead use the standard definition of transitive closure and the accompanying proof of well-foundness defined in `Relation.Binary.Construct.Closure.Transitive`.

Deprecated names
----------------

* In `Relation.Binary.Construct.Closure.Reflexive`:
  ```agda
  Refl ↦ ReflClosure
  ```

* In `Relation.Binary.Construct.Closure.Transitive`:
  ```agda
  Plus′ ↦ TransClosure
  ```

New modules
-----------

* Added `Reflection.Traversal` for generic de Bruijn-aware traversals of reflected terms.
* Added `Reflection.DeBruijn` with weakening, strengthening and free variable operations
  on reflected terms.

Other major changes
-------------------

Other minor additions
---------------------

* Added `Reflection.TypeChecking.Format.errorPartFmt`.

* Added new records to `Algebra.Bundles`:
  ```agda
  RawNearSemiring c ℓ : Set (suc (c ⊔ ℓ))
  RawLattice c ℓ : Set (suc (c ⊔ ℓ))
  CancellativeCommutativeSemiring c ℓ : Set (suc (c ⊔ ℓ))
  ```

* Added new records to `Algebra.Morphism.Structures`:
  ```agda
  IsNearSemiringHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsNearSemiringMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsNearSemiringIsomorphism  (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  IsSemiringHomomorphism  (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsSemiringMonomorphism  (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsSemiringIsomorphism   (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  IsLatticeHomomorphism  (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsLatticeMonomorphism  (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂)
  IsLatticeIsomorphism   (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)
  ```

* Added new proofs to `Relation.Binary.Construct.Closure.Transitive`:
  ```agda
  reflexive   : Reflexive _∼_ → Reflexive _∼⁺_
  symmetric   : Symmetric _∼_ → Symmetric _∼⁺_
  transitive  : Transitive _∼⁺_
  wellFounded : WellFounded _∼_ → WellFounded _∼⁺_

* Added new definitions to `Algebra.Definitions`:
  ```agda
  AlmostLeftCancellative  e _•_ = ∀ {x} y z → ¬ x ≈ e → (x • y) ≈ (x • z) → y ≈ z
  AlmostRightCancellative e _•_ = ∀ {x} y z → ¬ x ≈ e → (y • x) ≈ (z • x) → y ≈ z
  AlmostCancellative      e _•_ = AlmostLeftCancellative e _•_ × AlmostRightCancellative e _•_
  ```

* Added new record to `Algebra.Structures`:
  ```agda
  IsCancellativeCommutativeSemiring (+ * : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ)
  ```

* Add version to library name
