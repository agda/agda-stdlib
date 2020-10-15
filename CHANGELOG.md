Version 1.5-dev
===============

The library has been tested using Agda 2.6.1 and 2.6.1.1.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

* The internal build utilities package `lib.cabal` has been renamed
  `agda-stdlib-utils.cabal` to avoid potential conflict or confusion.
  Please note that the package is not intended for external use.

Deprecated modules
------------------

Deprecated names
----------------

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

* Add version to library name

* Add new properties to `Data.Vec.Properties`:
  ```agda
  take-distr-zipWith : ∀ {m n} → (f : A → B → C) →
                       (u : Vec A (m + n)) → (v : Vec B (m + n)) →
                       take m (zipWith f u v) ≡ zipWith f (take m u) (take m v)
  take-distr-map : ∀ {n} → (f : A → B) → (m : ℕ) → (v : Vec A (m + n)) →
                   take m (map f v) ≡ map f (take m v)
  drop-distr-zipWith : ∀ {m n} → (f : A → B → C) →
                       (u : Vec A (m + n)) → (v : Vec B (m + n)) →
                       drop m (zipWith f u v) ≡ zipWith f (drop m u) (drop m v)
  drop-distr-map : ∀ {n} → (f : A → B) → (m : ℕ) → (v : Vec A (m + n)) →
                   drop m (map f v) ≡ map f (drop m v)
  take-drop-id : ∀ {n} → (m : ℕ) → (v : Vec A (m + n)) → take m v ++ drop m v ≡ v
  zipWith-replicate : ∀ {n : ℕ} (_⊕_ : A → B → C) (x : A) (y : B) →
                      zipWith {n = n} _⊕_ (replicate x) (replicate y) ≡ replicate (x ⊕ y)
  ```
