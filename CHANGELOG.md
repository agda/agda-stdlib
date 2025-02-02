Version 2.3-dev
===============

The library has been tested using Agda 2.7.0 and 2.7.0.1.

Highlights
----------

* A major overhaul of the `Function` hierarchy sees the systematic development
  and use of theory of the left inverse to a given `Surjective` function `f`, in
  `Function.Consequences.Section`, up to and including full symmetry of `Bijection`, in
  `Function.Properties.Bijection`.

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

* In `Algebra.Definitions.RawMagma`:
  ```agda
  _∣∣_   ↦  _∥_
  _∤∤_    ↦  _∦_
  ```

* In `Algebra.Properties.Magma.Divisibility`:
  ```agda
  ∣∣-sym       ↦  ∥-sym
  ∣∣-respˡ-≈   ↦  ∥-respˡ-≈
  ∣∣-respʳ-≈   ↦  ∥-respʳ-≈
  ∣∣-resp-≈    ↦  ∥-resp-≈
  ∤∤-sym  -≈    ↦  ∦-sym
  ∤∤-respˡ-≈    ↦  ∦-respˡ-≈
  ∤∤-respʳ-≈    ↦  ∦-respʳ-≈
  ∤∤-resp-≈     ↦  ∦-resp-≈
  ```

* In `Algebra.Properties.Monoid.Divisibility`:
  ```agda
  ∣∣-refl            ↦  ∥-refl
  ∣∣-reflexive       ↦  ∥-reflexive
  ∣∣-isEquivalence   ↦  ∥-isEquivalence
  ```

* In `Algebra.Properties.Semigroup.Divisibility`:
  ```agda
  ∣∣-trans   ↦  ∥-trans
  ```

* In `Function.Bundles.IsSurjection`:
  ```agda
  to⁻      ↦  Function.Structures.IsSurjection.section
  to∘to⁻   ↦  Function.Structures.IsSurjection.strictlyInverseˡ
  ```

* In `Function.Construct.Symmetry`:
  ```agda
  injective       ↦  Function.Consequences.Section.injective
  surjective      ↦  Function.Consequences.Section.surjective
  bijective       ↦  Function.Consequences.Section.bijective
  isBijection     ↦  isBijectionWithoutCongruence
  isBijection-≡   ↦  isBijectionWithoutCongruence
  bijection-≡     ↦  bijectionWithoutCongruence
  ```

* In `Function.Properties.Bijection`:
  ```agda
  sym-≡   ↦  sym
  ```

* In `Function.Properties.Surjection`:
  ```agda
  injective⇒to⁻-cong   ↦  Function.Construct.Symmetry.bijectionWithoutCongruence
  ```

New modules
-----------

Additions to existing modules
-----------------------------

* In `Algebra.Construct.Pointwise`:
  ```agda
  isNearSemiring                  : IsNearSemiring _≈_ _+_ _*_ 0# →
                                    IsNearSemiring (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#)
  isSemiringWithoutOne            : IsSemiringWithoutOne _≈_ _+_ _*_ 0# →
                                    IsSemiringWithoutOne (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#)
  isCommutativeSemiringWithoutOne : IsCommutativeSemiringWithoutOne _≈_ _+_ _*_ 0# →
                                    IsCommutativeSemiringWithoutOne (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#)
  isCommutativeSemiring           : IsCommutativeSemiring _≈_ _+_ _*_ 0# 1# →
                                    IsCommutativeSemiring (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#) (lift₀ 1#)
  isIdempotentSemiring            : IsIdempotentSemiring _≈_ _+_ _*_ 0# 1# →
                                    IsIdempotentSemiring (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#) (lift₀ 1#)
  isKleeneAlgebra                 : IsKleeneAlgebra _≈_ _+_ _*_ _⋆ 0# 1# →
                                    IsKleeneAlgebra (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₁ _⋆) (lift₀ 0#) (lift₀ 1#)
  isQuasiring                     : IsQuasiring _≈_ _+_ _*_ 0# 1# →
                                    IsQuasiring (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₀ 0#) (lift₀ 1#)
  isCommutativeRing               : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1# →
                                    IsCommutativeRing (liftRel _≈_) (lift₂ _+_) (lift₂ _*_) (lift₁ -_) (lift₀ 0#) (lift₀ 1#)
  commutativeMonoid               : CommutativeMonoid c ℓ → CommutativeMonoid (a ⊔ c) (a ⊔ ℓ)
  nearSemiring                    : NearSemiring c ℓ → NearSemiring (a ⊔ c) (a ⊔ ℓ)
  semiringWithoutOne              : SemiringWithoutOne c ℓ → SemiringWithoutOne (a ⊔ c) (a ⊔ ℓ)
  commutativeSemiringWithoutOne   : CommutativeSemiringWithoutOne c ℓ → CommutativeSemiringWithoutOne (a ⊔ c) (a ⊔ ℓ)
  commutativeSemiring             : CommutativeSemiring c ℓ → CommutativeSemiring (a ⊔ c) (a ⊔ ℓ)
  idempotentSemiring              : IdempotentSemiring c ℓ → IdempotentSemiring (a ⊔ c) (a ⊔ ℓ)
  kleeneAlgebra                   : KleeneAlgebra c ℓ → KleeneAlgebra (a ⊔ c) (a ⊔ ℓ)
  quasiring                       : Quasiring c ℓ → Quasiring (a ⊔ c) (a ⊔ ℓ)
  commutativeRing                 : CommutativeRing c ℓ → CommutativeRing (a ⊔ c) (a ⊔ ℓ)
  ```

* In `Function.Bundles.Bijection`:
  ```agda
  section          : B → A
  inverseˡ         : Inverseˡ _≈₁_ _≈₂_ to section
  strictlyInverseˡ : StrictlyInverseˡ _≈₂_ to section
  inverseʳ         : Inverseʳ _≈₁_ _≈₂_ to section
  strictlyInverseʳ : StrictlyInverseʳ _≈₁_ to section
  ```

* In `Function.Bundles.LeftInverse`:
  ```agda
  surjective       : Surjective _≈₁_ _≈₂_ to
  surjection       : Surjection From To
  ```

* In `Function.Bundles.RightInverse`:
  ```agda
  isInjection      : IsInjection to
  injective        : Injective _≈₁_ _≈₂_ to
  injection        : Injection From To
  ```

* In `Function.Bundles.Surjection`:
  ```agda
  section          : B → A
  inverseˡ         : Inverseˡ _≈₁_ _≈₂_ to section
  strictlyInverseˡ : StrictlyInverseˡ _≈₂_ to section
  ```

* In `Function.Consequences` and `Function.Consequences.Setoid`:
  the theory of the left inverse of a surjective function
  ```agda
  module Section (surj :  Surjective ≈₁ ≈₂ f)
  ```

* In `Function.Construct.Symmetry`:
  ```agda
  isBijectionWithoutCongruence : (IsBijection ≈₁ ≈₂ f) → IsBijection ≈₂ ≈₁ section
  bijectionWithoutCongruence   : (Bijection R S) → Bijection S R
  ```

* In `Function.Properties.Bijection`:
  ```agda
  sym : Bijection S T → Bijection T S
  ```

* In `Function.Structures.IsBijection`:
  ```agda
  section          : B → A
  inverseˡ         : Inverseˡ _≈₁_ _≈₂_ f section
  strictlyInverseˡ : StrictlyInverseˡ _≈₂_ f section
  inverseʳ         : Inverseʳ _≈₁_ _≈₂_ f section
  strictlyInverseʳ : StrictlyInverseʳ _≈₁_ f section
  ```

* In `Function.Structures.IsLeftInverse`:
  ```agda
  surjective : Surjective _≈₁_ _≈₂_ to
  ```

* In `Function.Structures.IsRightInverse`:
  ```agda
  injective   : Injective _≈₁_ _≈₂_ to
  isInjection : IsInjection to
  ```

* In `Function.Structures.IsSurjection`:
  ```agda
  section          : B → A
  inverseˡ         : Inverseˡ _≈₁_ _≈₂_ f section
  strictlyInverseˡ : StrictlyInverseˡ _≈₂_ f section
  ```

