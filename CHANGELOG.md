Version 2.3-dev
===============

The library has been tested using Agda 2.7.0 and 2.7.0.1.

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

New modules
-----------

* `Algebra.Properties.IntegralSemiring`, with:
  ```agda
  x≉0∧y≉0⇒xẏ≉0 :  x ≉ 0# → y ≉ 0# → x * y ≉ 0#
  ```

* `Algebra.Properties.Semiring.Triviality`, with:
  ```agda
  trivial⇒x≈0 : Trivial → ∀ x → x ≈ 0#
  ```

Additions to existing modules
-----------------------------

* In `Algebra.Bundles`:
  ```agda
  IntegralCommutativeRing     : (c ℓ : Level) → Set _
  IntegralCommutativeSemiring : (c ℓ : Level) → Set _
  IntegralDomain              : (c ℓ : Level) → Set _
  IntegralRing                : (c ℓ : Level) → Set _
  IntegralSemiring            : (c ℓ : Level) → Set _
  ```

* In `Algebra.Consequences.Base`:
  ```agda
  integral⇒noZeroDivisors     : Integral _≈_ 1# 0# _∙_ → 1# ≉ 0# →
                                NoZeroDivisors _≈_ 0# _∙_
  noZeroDivisors⇒x≉0∧y≉0⇒xẏ≉0 : NoZeroDivisors _≈_ 0# _∙_ →
                                x ≉ 0# → y ≉ 0# → (x ∙ y) ≉ 0#
  ```

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

* In `Algebra.Definitions`:
  ```agda
  NoZeroDivisors : A → Op₂ A → Set _
  Integral       : A → A → Op₂ A → Set _
  ```
  (see [discussion on issue #2554](https://github.com/agda/agda-stdlib/issues/2554))

* In `Algebra.Definitions.RawSemiring`:
  ```agda
  Trivial : Set _
  ```
  (see [discussion on issue #2554](https://github.com/agda/agda-stdlib/issues/2554))

* In `Algebra.Structures`:
  ```agda
  IsIntegralCommutativeSemiring : (+ * : Op₂ A) (0# 1# : A) → Set _
  IsIntegralCommutativeRing     : (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A) → Set _
  IsIntegralDomain              : (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A) → Set _
  IsIntegralSemiring            : (+ * : Op₂ A) (0# 1# : A) → Set _
  IsIntegralRing                : (+ * : Op₂ A) (- : Op₁ A) (0# 1# : A) → Set _
  ```
