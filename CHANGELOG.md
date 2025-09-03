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

* `Relation.Binary.Properties.PartialSetoid` to systematise properties of a PER

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

* In `Data.Fin.Subset`:
  ```agda
  _⊇_ : Subset n → Subset n → Set
  _⊉_ : Subset n → Subset n → Set
  _⊃_ : Subset n → Subset n → Set
  _⊅_ : Subset n → Subset n → Set

  ```

* In `Data.Fin.Subset.Induction`:
  ```agda
  ⊃-Rec : RecStruct (Subset n) ℓ ℓ
  ⊃-wellFounded : WellFounded _⊃_
  ```

* In `Data.Fin.Subset.Properties`
  ```agda
  p⊆q⇒∁p⊇∁q : p ⊆ q → ∁ p ⊇ ∁ q
  ∁p⊆∁q⇒p⊇q : ∁ p ⊆ ∁ q → p ⊇ q
  p⊂q⇒∁p⊃∁q : p ⊂ q → ∁ p ⊃ ∁ q
  ∁p⊂∁q⇒p⊃q : ∁ p ⊂ ∁ q → p ⊃ q
  ```

* In `Data.List.Properties`:
  ```agda
  map-applyUpTo : ∀ (f : ℕ → A) (g : A → B) n → map g (applyUpTo f n) ≡ applyUpTo (g ∘ f) n
  map-applyDownFrom : ∀ (f : ℕ → A) (g : A → B) n → map g (applyDownFrom f n) ≡ applyDownFrom (g ∘ f) n
  map-upTo : ∀ (f : ℕ → A) n → map f (upTo n) ≡ applyUpTo f n
  map-downFrom : ∀ (f : ℕ → A) n → map f (downFrom n) ≡ applyDownFrom f n
  ```

* In `Data.List.Relation.Binary.Permutation.Propositional`:
  ```agda
  ↭⇒↭ₛ′ : IsEquivalence _≈_ → _↭_ ⇒ _↭ₛ′_
  ```

* In `Data.List.Relation.Binary.Permutation.Propositional.Properties`:
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

* In `Relation.Nullary.Reflects`:
  ```agda
  ⊤-reflects : Reflects (⊤ {a}) true
  ⊥-reflects : Reflects (⊥ {a}) false
	```
* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  cartesianProductWith⁻ : ∀ f →
                          f Preserves₂ _≈₁_ ⟶ _≈₂_ ⟶ _≡_ →
                          ∀ xs ys →
                          All P (cartesianProductWith f xs ys) →
                          (∀ {x y} → x ∈₁ xs → y ∈₂ ys → P (f x y))
  cartesianProduct⁻ : _,_ Preserves₂ _≈₁_ ⟶ _≈₂_ ⟶ _≡_ →
                      ∀ xs ys →
                      All P (cartesianProduct xs ys) →
                      (∀ {x y} → x ∈₁ xs → y ∈₂ ys → P (x , y))
  ```
