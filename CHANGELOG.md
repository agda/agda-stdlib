Version 2.1-dev
===============

The library has been tested using Agda 2.6.4 and 2.6.4.1.

Highlights
----------

Bug-fixes
---------

* Fix statement of `Data.Vec.Properties.toList-replicate`, where `replicate`
  was mistakenly applied to the level of the type `A` instead of the
  variable `x` of type `A`.

Non-backwards compatible changes
--------------------------------

* The modules and morphisms in `Algebra.Module.Morphism.Structures` are now
  parametrized by _raw_ bundles rather than lawful bundles, in line with other
  modules defining morphism structures.
* The definitions in `Algebra.Module.Morphism.Construct.Composition` are now
  parametrized by _raw_ bundles, and as such take a proof of transitivity.
* The definitions in `Algebra.Module.Morphism.Construct.Identity` are now
  parametrized by _raw_ bundles, and as such take a proof of reflexivity.

Other major improvements
------------------------

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Properties.Semiring.Mult`:
  ```agda
  1×-identityʳ  ↦  ×-homo-1
  ```

* In `Data.Nat.Divisibility.Core`:
  ```agda
  *-pres-∣  ↦  Data.Nat.Divisibility.*-pres-∣
  ```

New modules
-----------

* `Algebra.Module.Bundles.Raw`: raw bundles for module-like algebraic structures

Additions to existing modules
-----------------------------

* Exporting more `Raw` substructures from `Algebra.Bundles.Ring`:
  ```agda
  rawNearSemiring   : RawNearSemiring _ _
  rawRingWithoutOne : RawRingWithoutOne _ _
  +-rawGroup        : RawGroup _ _
  ```

* In `Algebra.Module.Bundles`, raw bundles are re-exported and the bundles expose their raw counterparts.

* In `Algebra.Module.Construct.DirectProduct`:
  ```agda
  rawLeftSemimodule  : RawLeftSemimodule R m ℓm → RawLeftSemimodule m′ ℓm′ → RawLeftSemimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawLeftModule      : RawLeftModule R m ℓm → RawLeftModule m′ ℓm′ → RawLeftModule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawRightSemimodule : RawRightSemimodule R m ℓm → RawRightSemimodule m′ ℓm′ → RawRightSemimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawRightModule     : RawRightModule R m ℓm → RawRightModule m′ ℓm′ → RawRightModule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawBisemimodule    : RawBisemimodule R m ℓm → RawBisemimodule m′ ℓm′ → RawBisemimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawBimodule        : RawBimodule R m ℓm → RawBimodule m′ ℓm′ → RawBimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawSemimodule      : RawSemimodule R m ℓm → RawSemimodule m′ ℓm′ → RawSemimodule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  rawModule          : RawModule R m ℓm → RawModule m′ ℓm′ → RawModule R (m ⊔ m′) (ℓm ⊔ ℓm′)
  ```

* In `Algebra.Module.Construct.TensorUnit`:
  ```agda
  rawLeftSemimodule  : RawLeftSemimodule _ c ℓ
  rawLeftModule      : RawLeftModule _ c ℓ
  rawRightSemimodule : RawRightSemimodule _ c ℓ
  rawRightModule     : RawRightModule _ c ℓ
  rawBisemimodule    : RawBisemimodule _ _ c ℓ
  rawBimodule        : RawBimodule _ _ c ℓ
  rawSemimodule      : RawSemimodule _ c ℓ
  rawModule          : RawModule _ c ℓ
  ```

* In `Algebra.Module.Construct.Zero`:
  ```agda
  rawLeftSemimodule  : RawLeftSemimodule R c ℓ
  rawLeftModule      : RawLeftModule R c ℓ
  rawRightSemimodule : RawRightSemimodule R c ℓ
  rawRightModule     : RawRightModule R c ℓ
  rawBisemimodule    : RawBisemimodule R c ℓ
  rawBimodule        : RawBimodule R c ℓ
  rawSemimodule      : RawSemimodule R c ℓ
  rawModule          : RawModule R c ℓ
  ```

* In `Algebra.Properties.Monoid.Mult`:
  ```agda
  ×-homo-0 : ∀ x → 0 × x ≈ 0#
  ×-homo-1 : ∀ x → 1 × x ≈ x
  ```

* In `Algebra.Properties.Semiring.Mult`:
  ```agda
  ×-homo-0#     : ∀ x → 0 × x ≈ 0# * x
  ×-homo-1#     : ∀ x → 1 × x ≈ 1# * x
  idem-×-homo-* : (_*_ IdempotentOn x) → (m × x) * (n × x) ≈ (m ℕ.* n) × x
  ```

* In `Data.Fin.Properties`:
  ```agda
  nonZeroIndex : Fin n → ℕ.NonZero n
  ```

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  All-catMaybes⁺ : All (Maybe.All P) xs → All P (catMaybes xs)
  Any-catMaybes⁺ : All (Maybe.Any P) xs → All P (catMaybes xs)
  ```

* In `Data.List.Relation.Unary.AllPairs.Properties`:
  ```agda
  catMaybes⁺ : AllPairs (Pointwise R) xs → AllPairs R (catMaybes xs)
  tabulate⁺-< : (i < j → R (f i) (f j)) → AllPairs R (tabulate f)
  ```

* In `Data.Maybe.Relation.Binary.Pointwise`:
  ```agda
  pointwise⊆any : Pointwise R (just x) ⊆ Any (R x)
  ```

* In `Data.Nat.Divisibility`:
  ```agda
  quotient≢0       : m ∣ n → .{{NonZero n}} → NonZero quotient

  m∣n⇒n≡quotient*m : m ∣ n → n ≡ quotient * m
  m∣n⇒n≡m*quotient : m ∣ n → n ≡ m * quotient
  quotient-∣       : m ∣ n → quotient ∣ n
  quotient>1       : m ∣ n → m < n → 1 < quotient
  quotient-<       : m ∣ n → .{{NonTrivial m}} → .{{NonZero n}} → quotient < n
  n/m≡quotient     : m ∣ n → .{{_ : NonZero m}} → n / m ≡ quotient

  m/n≡0⇒m<n    : .{{_ : NonZero n}} → m / n ≡ 0 → m < n
  m/n≢0⇒n≤m    : .{{_ : NonZero n}} → m / n ≢ 0 → n ≤ m

  nonZeroDivisor : DivMod dividend divisor → NonZero divisor
  ```

* Added new proofs in `Data.Nat.Properties`:
  ```agda
  m≤n+o⇒m∸n≤o : ∀ m n {o} → m ≤ n + o → m ∸ n ≤ o
  m<n+o⇒m∸n<o : ∀ m n {o} → .{{NonZero o}} → m < n + o → m ∸ n < o
  pred-cancel-≤ : pred m ≤ pred n → (m ≡ 1 × n ≡ 0) ⊎ m ≤ n
  pred-cancel-< : pred m < pred n → m < n
  pred-injective : .{{NonZero m}} → .{{NonZero n}} → pred m ≡ pred n → m ≡ n
  pred-cancel-≡ : pred m ≡ pred n → ((m ≡ 0 × n ≡ 1) ⊎ (m ≡ 1 × n ≡ 0)) ⊎ m ≡ n
  ```

* Added new functions in `Data.String.Base`:
  ```agda
  map : (Char → Char) → String → String
  ```

* In `Function.Bundles`, added `_⟶ₛ_` as a synonym for `Func` that can
  be used infix.

* Added new definitions in `Relation.Binary`
  ```
  Stable          : Pred A ℓ → Set _
  ```

* Added new definitions in `Relation.Nullary`
  ```
  Recomputable    : Set _
  WeaklyDecidable : Set _
  ```

* Added new definitions in `Relation.Unary`
  ```
  Stable          : Pred A ℓ → Set _
  WeaklyDecidable : Pred A ℓ → Set _
  ```

* Added new proof in `Relation.Nullary.Decidable`:
  ```agda
  ⌊⌋-map′ : (a? : Dec A) → ⌊ map′ t f a? ⌋ ≡ ⌊ a? ⌋
  ```

* In `Data.Vec.Functional.Algebra.Base`
```agda
  _≈ᴹ_ : Rel (Vector Carrier n) ℓ
  _+ᴹ_ : Op₂ $ Vector Carrier n
  0ᴹ : Vector Carrier n
  -ᴹ_ : Op₁ $ Vector Carrier n
  _*ₗ_ : Opₗ Carrier (Vector Carrier n)
```

* Added algebraic properties in `Data.Vec.Functional.Algebra.Properties`
```agda
  +ᴹ-cong : Congruent₂ (_+ᴹ_ {n})
  *ᴹ-cong : Congruent₂ (_*ᴹ_ {n})
  +ᴹ-assoc : Associative (_+ᴹ_ {n})
  *ᴹ-assoc : Associative (_*ᴹ_ {n})
  +ᴹ-comm : Commutative (_+ᴹ_ {n})
  *ᴹ-comm : Commutative (_*ᴹ_ {n})
  +ᴹ-identityˡ : LeftIdentity (0ᴹ {n}) _+ᴹ_
  *ᴹ-identityˡ : LeftIdentity (1ᴹ {n}) _*ᴹ_
  +ᴹ-identityʳ : RightIdentity (0ᴹ {n}) _+ᴹ_
  *ᴹ-identityʳ : RightIdentity (1ᴹ {n}) _*ᴹ_
  +ᴹ-identity : Identity (0ᴹ {n}) _+ᴹ_
  *ᴹ-identity : Identity (1ᴹ {n}) _*ᴹ_
  -ᴹ‿cong : Congruent₁ (-ᴹ_ {n})
  -ᴹ‿inverseˡ : AD'.LeftInverse (0ᴹ {n}) -ᴹ_ _+ᴹ_
  -ᴹ‿inverseʳ : AD'.RightInverse (0ᴹ {n}) -ᴹ_ _+ᴹ_
  -ᴹ‿inverse : AD'.Inverse (0ᴹ {n}) -ᴹ_ _+ᴹ_
  *ₗ-cong : LD.Congruent SR._≈_ (_*ₗ_ {n})
  *ₗ-zeroˡ : LD.LeftZero SR.0# (0ᴹ {n}) _*ₗ_
  *ₗ-distribʳ : _*ₗ_ LD.DistributesOverʳ SR._+_ ⟶ (_+ᴹ_ {n})
  *ₗ-identityˡ : LD.LeftIdentity SR.1# (_*ₗ_ {n})
  *ₗ-assoc : LD.Associative SR._*_ (_*ₗ_ {n})
  *ₗ-zeroʳ : LD.RightZero (0ᴹ {n}) _*ₗ_
  *ₗ-distribˡ : _*ₗ_ LD.DistributesOverˡ (_+ᴹ_ {n})
  *ᵣ-cong : RD.Congruent SR._≈_ (_*ᵣ_ {n})
  *ᵣ-distribˡ : _*ᵣ_ RD.DistributesOverˡ SR._+_ ⟶ (_+ᴹ_ {n})
  *ᵣ-zeroˡ : RD.LeftZero (0ᴹ {n}) _*ᵣ_
  *ᵣ-identityʳ : RD.RightIdentity SR.1# (_*ᵣ_ {n})
  *ᵣ-assoc : RD.Associative SR._*_ (_*ᵣ_ {n})
  *ᵣ-zeroʳ : RD.RightZero SR.0# (0ᴹ {n}) _*ᵣ_
  *ᵣ-distribʳ : _*ᵣ_ RD.DistributesOverʳ (_+ᴹ_ {n})
  *ₗ-*ᵣ-assoc : BD.Associative (_*ₗ_ {n}) _*ᵣ_
  *ᴹ-zeroˡ : AD'.LeftZero (0ᴹ {n}) _*ᴹ_
  *ᴹ-zeroʳ : AD'.RightZero (0ᴹ {n}) _*ᴹ_
  *ᴹ-zero : AD'.Zero (0ᴹ {n}) _*ᴹ_
  *ᴹ-+ᴹ-distribˡ : (_*ᴹ_ {n}) AD'.DistributesOverˡ _+ᴹ_
  *ᴹ-+ᴹ-distribʳ : (_*ᴹ_ {n}) AD'.DistributesOverʳ _+ᴹ_
  *ᴹ-+ᴹ-distrib : (_*ᴹ_ {n}) AD'.DistributesOver _+ᴹ_
```

* Added structures in `Data.Vec.Functional.Algebra.Properties`
```agda
  isMagma : IsMagma (_+ᴹ_ {n})
  *ᴹ-isMagma : IsMagma (_*ᴹ_ {n})
  isCommutativeMagma : IsCommutativeMagma (_+ᴹ_ {n})
  isSemigroup : IsSemigroup (_+ᴹ_ {n})
  *ᴹ-isSemigroup : IsSemigroup (_*ᴹ_ {n})
  isCommutativeSemigroup : IsCommutativeSemigroup (_+ᴹ_ {n})
  isMonoid : IsMonoid (_+ᴹ_ {n}) 0ᴹ
  *ᴹ-isMonoid : IsMonoid (_*ᴹ_ {n}) 1ᴹ
  isCommutativeMonoid : IsCommutativeMonoid (_+ᴹ_ {n}) 0ᴹ
  isGroup : IsGroup (_+ᴹ_ {n}) 0ᴹ -ᴹ_
  isAbelianGroup : IsAbelianGroup (_+ᴹ_ {n}) 0ᴹ -ᴹ_
  isPreleftSemimodule : IsPreleftSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_
  isPrerightSemimodule : IsPrerightSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ᵣ_
  isRightSemimodule : IsRightSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ᵣ_
  isBisemimodule : IsBisemimodule semiring semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_ _*ᵣ_
  isRightModule : IsRightModule ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ᵣ_
  isBimodule : IsBimodule ring ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_
  isLeftSemimodule : IsLeftSemimodule semiring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ _*ₗ_
  isLeftModule : IsLeftModule ring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_
  isModule : IsModule cring (_≈ᴹ_ {n}) _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_
  +ᴹ-*-isNearSemiring : IsNearSemiring (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ
  +ᴹ-*-isSemiringWithoutOne : IsSemiringWithoutOne (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ
  +ᴹ-*-isCommutativeSemiringWithoutOne : IsCommutativeSemiringWithoutOne (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ
  +ᴹ-*-isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ 1ᴹ
  +ᴹ-*-isSemiring : IsSemiring (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ 1ᴹ
  +ᴹ-*-isCommutativeSemiring : IsCommutativeSemiring (_+ᴹ_ {n}) _*ᴹ_ 0ᴹ 1ᴹ
  +ᴹ-*-isRingWithoutOne : IsRingWithoutOne (_+ᴹ_ {n}) _*ᴹ_ -ᴹ_ 0ᴹ
  +ᴹ-*-isRing : IsRing (_+ᴹ_ {n}) _*ᴹ_ -ᴹ_ 0ᴹ 1ᴹ
  +ᴹ-*-isCommutativeRing : IsCommutativeRing (_+ᴹ_ {n}) _*ᴹ_ -ᴹ_ 0ᴹ 1ᴹ
```

* Added bundles in `Data.Vec.Functional.Algebra.Properties`
```agda
  magma : ℕ → Magma _ _
  *ᴹ-magma : ℕ → Magma _ _
  commutativeMagma : ℕ → CommutativeMagma _ _
  semigroup : ℕ → Semigroup _ _
  *ᴹ-semigroup : ℕ → Semigroup _ _
  commutativeSemigroup : ℕ → CommutativeSemigroup _ _
  monoid : ℕ → Monoid _ _
  *ᴹ-monoid : ℕ → Monoid _ _
  commutativeMonoid : ℕ → CommutativeMonoid _ _
  group : ℕ → Group _ _
  leftSemimodule : ℕ → LeftSemimodule _ _ _
  leftModule : ℕ → LeftModule _ _ _
  bisemimodule : ℕ → Bisemimodule _ _ _ _
  rightModule : ℕ → RightModule _ _ _
  bimodule : ℕ → Bimodule _ _ _ _
  module' : ℕ → Module _ _ _
  +ᴹ-*-nearSemiring : ℕ → NearSemiring _ _
  +ᴹ-*-semiringWithoutOne : ℕ → SemiringWithoutOne _ _
  +ᴹ-*-commutativeSemiringWithoutOne : ℕ → CommutativeSemiringWithoutOne _ _
  +ᴹ-*-semiringWithoutAnnihilatingZero : ℕ → SemiringWithoutAnnihilatingZero _ _
  +ᴹ-*-semiring : ℕ → Semiring _ _
  +ᴹ-*-commutativeSemiring : ℕ → CommutativeSemiring _ _
  +ᴹ-*-ringWithoutOne : ℕ → RingWithoutOne _ _
```
