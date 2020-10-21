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

* The definition of `Data.Integer.Base`'s `_⊖_` was changed to use
  builtin operations, making it much faster.

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

* Added new proofs in `Data.Integer.Properties`:
  ```agda
  [1+m]⊖[1+n]≡m⊖n : suc m ⊖ suc n ≡ m ⊖ n
  ⊖-≤             : m ≤ n → m ⊖ n ≡ - + (n ∸ m)
  -m+n≡n⊖m        : - (+ m) + + n ≡ n ⊖ m
  m-n≡m⊖n         : + m + (- + n) ≡ m ⊖ n
  ```

* Added new definition in `Data.Nat.Base`:
  ```agda
  _≤ᵇ_ : (m n : ℕ) → Bool
  ```

* Added new proofs in `Data.Nat.Properties`:
  ```agda
  ≤ᵇ⇒≤ : T (m ≤ᵇ n) → m ≤ n
  ≤⇒≤ᵇ : m ≤ n → T (m ≤ᵇ n)

  <ᵇ-reflects-< : Reflects (m < n) (m <ᵇ n)
  ≤ᵇ-reflects-≤ : Reflects (m ≤ n) (m ≤ᵇ n)
  ```

* Added new proof in `Relation.Nullary.Reflects`:
  ```agda
  fromEquivalence : (T b → P) → (P → T b) → Reflects P b
  ```
