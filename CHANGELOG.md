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

* In `Algebra.Module.Consequences`
  ```agda
  *ₗ-assoc+comm⇒*ᵣ-assoc      ↦  *ₗ-assoc∧comm⇒*ᵣ-assoc
  *ₗ-assoc+comm⇒*ₗ-*ᵣ-assoc   ↦  *ₗ-assoc∧comm⇒*ₗ-*ᵣ-assoc
  *ᵣ-assoc+comm⇒*ₗ-assoc      ↦  *ᵣ-assoc∧comm⇒*ₗ-assoc
  *ₗ-assoc+comm⇒*ₗ-*ᵣ-assoc   ↦  *ₗ-assoc∧comm⇒*ₗ-*ᵣ-assoc
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

New modules
-----------

* `Data.List.Base.{and|or|any|all}` have been lifted out into `Data.Bool.ListAction`.

* `Data.List.Base.{sum|product}` and their properties have been lifted out into `Data.Nat.ListAction` and `Data.Nat.ListAction.Properties`.

* `Data.List.Relation.Binary.Prefix.Propositional.Properties` showing the equivalence to left divisibility induced by the list monoid.

* `Data.List.Relation.Binary.Suffix.Propositional.Properties` showing the equivalence to right divisibility induced by the list monoid.

* `Data.Sign.Show` to show a sign

Additions to existing modules
-----------------------------

* In `Algebra.Properties.Semigroup` adding consequences for associativity for semigroups

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

* In `Relation.Nullary.Decidable.Core`:
  ```agda
  ⊤-dec : Dec {a} ⊤
  ⊥-dec : Dec {a} ⊥
  ```
