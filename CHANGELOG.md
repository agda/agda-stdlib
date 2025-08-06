Version 2.4-dev
===============

The library has been tested using Agda 2.8.0.

Highlights
----------

Bug-fixes
---------

* Fix a type error in `README.Data.Fin.Relation.Unary.Top` within the definition of `>-weakInduction`.

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

* The type of `Relation.Nullary.Negation.Core.contradiction-irr` has been further
  weakened so that the negated hypothesis `¬ A` is marked as irrelevant. This is
  safe to do, in view of `Relation.Nullary.Recomputable.Properties.¬-recompute`.

* Refactored usages of `+-∸-assoc 1` to `∸-suc` in:
  ```agda
  README.Data.Fin.Relation.Unary.Top
  Algebra.Properties.Semiring.Binomial
  Data.Fin.Subset.Properties
  Data.Nat.Binary.Subtraction
  Data.Nat.Combinatorics
  ```

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Properties.CommutativeSemigroup`:
  ```agda
  interchange  ↦   medial
  ```

New modules
-----------

* `Data.List.Relation.Binary.Permutation.Algorithmic{.Properties}` for the Choudhury and Fiore definition of permutation, and its equivalence with `Declarative` below.

* `Data.List.Relation.Binary.Permutation.Declarative{.Properties}` for the least congruence on `List` making `_++_` commutative, and its equivalence with the `Setoid` definition.

Additions to existing modules
-----------------------------

* In `Algebra.Properties.RingWithoutOne`:
  ```agda
  [-x][-y]≈xy : ∀ x y → - x * - y ≈ x * y
  ```

* In `Data.Fin.Permutation.Components`:
  ```agda
  transpose[i,i,j]≡j  : (i j : Fin n) → transpose i i j ≡ j
  transpose[i,j,j]≡i  : (i j : Fin n) → transpose i j j ≡ i
  transpose[i,j,i]≡j  : (i j : Fin n) → transpose i j i ≡ j
  transpose-transpose : transpose i j k ≡ l → transpose j i l ≡ k
  ```

* In `Data.Fin.Properties`:
  ```agda
  ≡-irrelevant : Irrelevant {A = Fin n} _≡_
  ≟-≡          : (eq : i ≡ j) → (i ≟ j) ≡ yes eq
  ≟-≡-refl     : (i : Fin n) → (i ≟ i) ≡ yes refl
  ≟-≢          : (i≢j : i ≢ j) → (i ≟ j) ≡ no i≢j
  ```

* In `Data.Nat.Properties`:
  ```agda
  ≟-≢   : (m≢n : m ≢ n) → (m ≟ n) ≡ no m≢n
  ∸-suc : m ≤ n → suc n ∸ m ≡ suc (n ∸ m)
  ```

* In `Data.Vec.Properties`:
  ```agda
  padRight-lookup : (m≤n : m ≤ n) (a : A) (xs : Vec A m) (i : Fin m) → lookup (padRight m≤n a xs) (inject≤ i m≤n) ≡ lookup xs i

  padRight-map : (f : A → B) (m≤n : m ≤ n) (a : A) (xs : Vec A m) → map f (padRight m≤n a xs) ≡ padRight m≤n (f a) (map f xs)

  padRight-zipWith : (f : A → B → C) (m≤n : m ≤ n) (a : A) (b : B) (xs : Vec A m) (ys : Vec B m) →
                   zipWith f (padRight m≤n a xs) (padRight m≤n b ys) ≡ padRight m≤n (f a b) (zipWith f xs ys)

  padRight-zipWith₁ : (f : A → B → C) (o≤m : o ≤ m) (m≤n : m ≤ n) (a : A) (b : B) (xs : Vec A m) (ys : Vec B o) →
                    zipWith f (padRight m≤n a xs) (padRight (≤-trans o≤m m≤n) b ys) ≡
                    padRight m≤n (f a b) (zipWith f xs (padRight o≤m b ys))

  padRight-take : (m≤n : m ≤ n) (a : A) (xs : Vec A m) .(n≡m+o : n ≡ m + o) → take m (cast n≡m+o (padRight m≤n a xs)) ≡ xs

  padRight-drop : (m≤n : m ≤ n) (a : A) (xs : Vec A m) .(n≡m+o : n ≡ m + o) → drop m (cast n≡m+o (padRight m≤n a xs)) ≡ replicate o a

  padRight-updateAt : (m≤n : m ≤ n) (x : A) (xs : Vec A m) (f : A → A) (i : Fin m) →
                    updateAt (padRight m≤n x xs) (inject≤ i m≤n) f ≡ padRight m≤n x (updateAt xs i f)
  ```

* In `Relation.Nullary.Negation.Core`
  ```agda
  ¬¬-η : A → ¬ ¬ A
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
