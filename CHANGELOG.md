Version 2.3-dev
===============

The library has been tested using Agda 2.7.0 and 2.7.0.1.

Highlights
----------

Bug-fixes
---------

* In `Algebra.Apartness.Structures`, renamed `sym` from `IsApartnessRelation`
  to `#-sym` in order to avoid overloaded projection.
  `irrefl` and `cotrans` are similarly renamed for the sake of consistency.

* In `Algebra.Definitions.RawMagma` and `Relation.Binary.Construct.Interior.Symmetric`,
  the record constructors `_,_` incorrectly had no declared fixity. They have been given
  the fixity `infixr 4 _,_`, consistent with that of `Data.Product.Base`.

* In `Data.Product.Function.Dependent.Setoid`, `left-inverse` defined a
  `RightInverse`.
  This has been deprecated in favor or `rightInverse`, and a corrected (and
  correctly-named) function `leftInverse` has been added.

* The implementation of `_IsRelatedTo_` in `Relation.Binary.Reasoning.Base.Partial`
  has been modified to correctly support equational reasoning at the beginning and the end.
  The detail of this issue is described in [#2677](https://github.com/agda/agda-stdlib/pull/2677). Since the names of constructors
  of `_IsRelatedTo_` are changed and the reduction behaviour of reasoning steps
  are changed, this modification is non-backwards compatible.

Non-backwards compatible changes
--------------------------------

* The implementation of `≤-total` in `Data.Nat.Properties` has been altered
  to use operations backed by primitives, rather than recursion, making it
  significantly faster. However, its reduction behaviour on open terms may have
  changed.

Minor improvements
------------------

* Moved the concept `Irrelevant` of irrelevance (h-proposition) from `Relation.Nullary`
  to its own dedicated module `Relation.Nullary.Irrelevant`.

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Definitions.RawMagma`:
  ```agda
  _∣∣_   ↦  _∥_
  _∤∤_    ↦  _∦_
  ```

* In `Algebra.Lattice.Properties.BooleanAlgebra`
  ```agda
  ⊥≉⊤   ↦  ¬⊥≈⊤
  ⊤≉⊥   ↦  ¬⊤≈⊥
  ```

* In `Algebra.Module.Consequences`
  ```agda
  *ₗ-assoc+comm⇒*ᵣ-assoc      ↦  *ₗ-assoc∧comm⇒*ᵣ-assoc
  *ₗ-assoc+comm⇒*ₗ-*ᵣ-assoc   ↦  *ₗ-assoc∧comm⇒*ₗ-*ᵣ-assoc
  *ᵣ-assoc+comm⇒*ₗ-assoc      ↦  *ᵣ-assoc∧comm⇒*ₗ-assoc
  *ₗ-assoc+comm⇒*ₗ-*ᵣ-assoc   ↦  *ₗ-assoc∧comm⇒*ₗ-*ᵣ-assoc
  ```

* In `Algebra.Modules.Structures.IsLeftModule`:
  ```agda
  uniqueˡ‿⁻ᴹ   ↦  Algebra.Module.Properties.LeftModule.inverseˡ-uniqueᴹ
  uniqueʳ‿⁻ᴹ   ↦  Algebra.Module.Properties.LeftModule.inverseʳ-uniqueᴹ
  ```

* In `Algebra.Modules.Structures.IsRightModule`:
  ```agda
  uniqueˡ‿⁻ᴹ   ↦  Algebra.Module.Properties.RightModule.inverseˡ-uniqueᴹ
  uniqueʳ‿⁻ᴹ   ↦  Algebra.Module.Properties.RightModule.inverseʳ-uniqueᴹ
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
  ∣-respʳ-≈    ↦ ∣ʳ-respʳ-≈
  ∣-respˡ-≈    ↦ ∣ʳ-respˡ-≈
  ∣-resp-≈     ↦ ∣ʳ-resp-≈
  x∣yx         ↦ x∣ʳyx
  xy≈z⇒y∣z     ↦ xy≈z⇒y∣ʳz
  ```

* In `Algebra.Properties.Monoid.Divisibility`:
  ```agda
  ∣∣-refl            ↦  ∥-refl
  ∣∣-reflexive       ↦  ∥-reflexive
  ∣∣-isEquivalence   ↦  ∥-isEquivalence
  ε∣_                ↦ ε∣ʳ_
  ∣-refl             ↦ ∣ʳ-refl
  ∣-reflexive        ↦ ∣ʳ-reflexive
  ∣-isPreorder       ↦ ∣ʳ-isPreorder
  ∣-preorder         ↦ ∣ʳ-preorder
  ```

* In `Algebra.Properties.Semigroup.Divisibility`:
  ```agda
  ∣∣-trans   ↦  ∥-trans
  ∣-trans    ↦  ∣ʳ-trans
  ```

* In `Algebra.Structures.Group`:
  ```agda
  uniqueˡ-⁻¹   ↦  Algebra.Properties.Group.inverseˡ-unique
  uniqueʳ-⁻¹   ↦  Algebra.Properties.Group.inverseʳ-unique
  ```

* In `Data.List.Base`:
  ```agda
  and       ↦  Data.Bool.ListAction.and
  or        ↦  Data.Bool.ListAction.or
  any       ↦  Data.Bool.ListAction.any
  all       ↦  Data.Bool.ListAction.all
  sum       ↦  Data.Nat.ListAction.sum
  product   ↦  Data.Nat.ListAction.product
  ```

* In `Data.List.Properties`:
  ```agda
  sum-++       ↦  Data.Nat.ListAction.Properties.sum-++
  ∈⇒∣product   ↦  Data.Nat.ListAction.Properties.∈⇒∣product
  product≢0    ↦  Data.Nat.ListAction.Properties.product≢0
  ∈⇒≤product   ↦  Data.Nat.ListAction.Properties.∈⇒≤product
  ```

* In `Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  sum-↭       ↦  Data.Nat.ListAction.Properties.sum-↭
  product-↭   ↦  Data.Nat.ListAction.Properties.product-↭
  ```

* In `Data.Product.Function.Dependent.Setoid`:
  ```agda
  left-inverse ↦ rightInverse
  ```

New modules
-----------

* `Algebra.Module.Properties.{Bimodule|LeftModule|RightModule}`.

* `Data.List.Base.{and|or|any|all}` have been lifted out into `Data.Bool.ListAction`.

* `Data.List.Base.{sum|product}` and their properties have been lifted out into `Data.Nat.ListAction` and `Data.Nat.ListAction.Properties`.

* `Data.List.Relation.Binary.Prefix.Propositional.Properties` showing the equivalence to left divisibility induced by the list monoid.

* `Data.List.Relation.Binary.Suffix.Propositional.Properties` showing the equivalence to right divisibility induced by the list monoid.

* `Data.Sign.Show` to show a sign

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

* In `Algebra.Modules.Properties`:
  ```agda
  inverseˡ-uniqueᴹ : x +ᴹ y ≈ 0ᴹ → x ≈ -ᴹ y
  inverseʳ-uniqueᴹ : x +ᴹ y ≈ 0ᴹ → y ≈ -ᴹ x
  ```

* In `Algebra.Properties.Magma.Divisibility`:
  ```agda
  ∣ˡ-respʳ-≈  : _∣ˡ_ Respectsʳ _≈_
  ∣ˡ-respˡ-≈  : _∣ˡ_ Respectsˡ _≈_
  ∣ˡ-resp-≈   : _∣ˡ_ Respects₂ _≈_
  x∣ˡxy       : ∀ x y → x ∣ˡ x ∙ y
  xy≈z⇒x∣ˡz   : ∀ x y {z} → x ∙ y ≈ z → x ∣ˡ z
  ```

* In `Algebra.Properties.Monoid.Divisibility`:
  ```agda
  ε∣ˡ_          : ∀ x → ε ∣ˡ x
  ∣ˡ-refl       : Reflexive _∣ˡ_
  ∣ˡ-reflexive  : _≈_ ⇒ _∣ˡ_
  ∣ˡ-isPreorder : IsPreorder _≈_ _∣ˡ_
  ∣ˡ-preorder   : Preorder a ℓ _
  ```

* In `Algebra.Properties.Semigroup.Divisibility`:
  ```agda
  ∣ˡ-trans     : Transitive _∣ˡ_
  x∣ʳy⇒x∣ʳzy   : x ∣ʳ y → x ∣ʳ z ∙ y
  x∣ʳy⇒xz∣ʳyz  : x ∣ʳ y → x ∙ z ∣ʳ y ∙ z
  x∣ˡy⇒zx∣ˡzy  : x ∣ˡ y → z ∙ x ∣ˡ z ∙ y
  x∣ˡy⇒x∣ˡyz   : x ∣ˡ y → x ∣ˡ y ∙ z
  ```

* In `Algebra.Properties.CommutativeSemigroup.Divisibility`:
  ```agda
  ∙-cong-∣ : x ∣ y → a ∣ b → x ∙ a ∣ y ∙ b
  ```

* In `Data.List.Properties`:
  ```agda
  map-applyUpTo : ∀ (f : ℕ → A) (g : A → B) n → map g (applyUpTo f n) ≡ applyUpTo (g ∘ f) n
  map-applyDownFrom : ∀ (f : ℕ → A) (g : A → B) n → map g (applyDownFrom f n) ≡ applyDownFrom (g ∘ f) n
  map-upTo : ∀ (f : ℕ → A) n → map f (upTo n) ≡ applyUpTo f n
  map-downFrom : ∀ (f : ℕ → A) n → map f (downFrom n) ≡ applyDownFrom f n
  ```

* In `Data.List.Relation.Binary.Permutation.PropositionalProperties`:
  ```agda
  filter-↭ : ∀ (P? : Pred.Decidable P) → xs ↭ ys → filter P? xs ↭ filter P? ys
  ```

* In `Data.Product.Function.Dependent.Propositional`:
  ```agda
  Σ-↪ : (I↪J : I ↪ J) → (∀ {j} → A (from I↪J j) ↪ B j) → Σ I A ↪ Σ J B
  ```

* In `Data.Product.Function.Dependent.Setoid`:
  ```agda
  rightInverse :
     (I↪J : I ↪ J) →
     (∀ {j} → RightInverse (A atₛ (from I↪J j)) (B atₛ j)) →
     RightInverse (I ×ₛ A) (J ×ₛ B)

  leftInverse :
    (I↩J : I ↩ J) →
    (∀ {i} → LeftInverse (A atₛ i) (B atₛ (to I↩J i))) →
    LeftInverse (I ×ₛ A) (J ×ₛ B)
  ```

* In `Data.Vec.Relation.Binary.Pointwise.Inductive`:
  ```agda
  zipWith-assoc : Associative _∼_ f → Associative (Pointwise _∼_) (zipWith {n = n} f)
  zipWith-identityˡ: LeftIdentity _∼_ e f → LeftIdentity (Pointwise _∼_) (replicate n e) (zipWith f)
  zipWith-identityʳ: RightIdentity _∼_ e f → RightIdentity (Pointwise _∼_) (replicate n e) (zipWith f)
  zipWith-comm : Commutative _∼_ f → Commutative (Pointwise _∼_) (zipWith {n = n} f)
  zipWith-cong : Congruent₂ _∼_ f → Pointwise _∼_ ws xs → Pointwise _∼_ ys zs → Pointwise _∼_ (zipWith f ws ys) (zipWith f xs zs)
  ```

* In `Relation.Binary.Construct.Add.Infimum.Strict`:
  ```agda
  <₋-accessible-⊥₋ : Acc _<₋_ ⊥₋
  <₋-accessible[_] : Acc _<_ x → Acc _<₋_ [ x ]
  <₋-wellFounded   : WellFounded _<_ → WellFounded _<₋_
  ```

* In `Relation.Nullary.Decidable.Core`:
  ```agda
  ⊤-dec : Dec {a} ⊤
  ⊥-dec : Dec {a} ⊥
  ```

* In `Relation.Nullary.Negation.Core`:
  ```agda
  contra-diagonal : (A → ¬ A) → ¬ A
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
