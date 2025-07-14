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
  ∷-ʳ++-eqFree ↦  Data.List.Properties.ʳ++-ʳ++-eqFree
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

* In `Data.Product.Nary.NonDependent`:
  ```agda
  Allₙ ↦ Pointwiseₙ
  ```

New modules
-----------

* `Algebra.Module.Properties.{Bimodule|LeftModule|RightModule}`.

* `Algebra.Morphism.Construct.DirectProduct`.

* `Data.List.Base.{and|or|any|all}` have been lifted out into `Data.Bool.ListAction`.

* `Data.List.Base.{sum|product}` and their properties have been lifted out into `Data.Nat.ListAction` and `Data.Nat.ListAction.Properties`.

* `Data.List.Relation.Binary.Prefix.Propositional.Properties` showing the equivalence to left divisibility induced by the list monoid.

* `Data.List.Relation.Binary.Suffix.Propositional.Properties` showing the equivalence to right divisibility induced by the list monoid.

* `Data.List.Sort.InsertionSort.{agda|Base|Properties}` defines insertion sort and proves properties of insertion sort such as Sorted and Permutation properties.

* `Data.List.Sort.MergenSort.{agda|Base|Properties}` is a refactor of the previous `Data.List.Sort.MergenSort`.

* `Data.Sign.Show` to show a sign.

* `Relation.Binary.Morphism.Construct.Product` to plumb in the (categorical) product structure on `RawSetoid`.

* `Relation.Binary.Properties.PartialSetoid` to systematise properties of a PER

* `Relation.Nullary.Recomputable.Core`

Additions to existing modules
-----------------------------

* In `Algebra.Consequences.Base`:
  ```agda
  module Congruence (_≈_ : Rel A ℓ) (cong : Congruent₂ _≈_ _∙_) (refl : Reflexive _≈_)
  where
    ∙-congˡ : LeftCongruent _≈_ _∙_
    ∙-congʳ : RightCongruent _≈_ _∙_
  ```

* In `Algebra.Consequences.Setoid`:
  ```agda
  module Congruence (cong : Congruent₂ _≈_ _∙_) where
    ∙-congˡ : LeftCongruent _≈_ _∙_
    ∙-congʳ : RightCongruent _≈_ _∙_
  ```

* In `Algebra.Construct.Initial`:
  ```agda
  assoc : Associative _≈_ _∙_
  idem  : Idempotent _≈_ _∙_
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

* In `Algebra.Properties.Semigroup` adding consequences for associativity for semigroups

```
  uv≈w⇒xu∙v≈xw          : ∀ x → (x ∙ u) ∙ v ≈ x ∙ w
  uv≈w⇒u∙vx≈wx          : ∀ x → u ∙ (v ∙ x) ≈ w ∙ x
  uv≈w⇒u[vx∙y]≈w∙xy     : ∀ x y → u ∙ ((v ∙ x) ∙ y) ≈ w ∙ (x ∙ y)
  uv≈w⇒x[uv∙y]≈x∙wy     : ∀ x y → x ∙ (u ∙ (v ∙ y)) ≈ x ∙ (w ∙ y)
  uv≈w⇒[x∙yu]v≈x∙yw     : ∀ x y → (x ∙ (y ∙ u)) ∙ v ≈ x ∙ (y ∙ w)
  uv≈w⇒[xu∙v]y≈x∙wy     : ∀ x y → ((x ∙ u) ∙ v) ∙ y ≈ x ∙ (w ∙ y)
  uv≈w⇒[xy∙u]v≈x∙yw     : ∀ x y → ((x ∙ y) ∙ u) ∙ v ≈ x ∙ (y ∙ w)
  uv≈w⇒xu∙vy≈x∙wy       : ∀ x y → (x ∙ u) ∙ (v ∙ y) ≈ x ∙ (w ∙ y)
  uv≈w⇒xy≈z⇒u[vx∙y]≈wz  : ∀ z → x ∙ y ≈ z → u ∙ ((v ∙ x) ∙ y) ≈ w ∙ z
  uv≈w⇒x∙wy≈x∙[u∙vy]    : x ∙ (w ∙ y) ≈ x ∙ (u ∙ (v ∙ y))
  [uv∙w]x≈u[vw∙x]       : ((u ∙ v) ∙ w) ∙ x ≈ u ∙ ((v ∙ w) ∙ x)
  [uv∙w]x≈u[v∙wx]       : ((u ∙ v) ∙ w) ∙ x ≈ u ∙ (v ∙ (w ∙ x))
  [u∙vw]x≈uv∙wx         : (u ∙ (v ∙ w)) ∙ x ≈ (u ∙ v) ∙ (w ∙ x)
  [u∙vw]x≈u[v∙wx]       : (u ∙ (v ∙ w)) ∙ x ≈ u ∙ (v ∙ (w ∙ x))
  uv∙wx≈u[vw∙x]         : (u ∙ v) ∙ (w ∙ x) ≈ u ∙ ((v ∙ w) ∙ x)
  uv≈wx⇒yu∙v≈yw∙x       : ∀ y → (y ∙ u) ∙ v ≈ (y ∙ w) ∙ x
  uv≈wx⇒u∙vy≈w∙xy       : ∀ y → u ∙ (v ∙ y) ≈ w ∙ (x ∙ y)
  uv≈wx⇒yu∙vz≈yw∙xz     : ∀ y z → (y ∙ u) ∙ (v ∙ z) ≈ (y ∙ w) ∙ (x ∙ z)
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

* In `Data.Bool.Properties`:
  ```agda
  if-eta : ∀ b → (if b then x else x) ≡ x
  if-idem-then : ∀ b → (if b then (if b then x else y) else y) ≡ (if b then x else y)
  if-idem-else : ∀ b → (if b then x else (if b then x else y)) ≡ (if b then x else y)
  if-swap-then : ∀ b c → (if b then (if c then x else y) else y) ≡ (if c then (if b then x else y) else y)
  if-swap-else : ∀ b c → (if b then x else (if c then x else y)) ≡ (if c then x else (if b then x else y))
  if-not : ∀ b → (if not b then x else y) ≡ (if b then y else x)
  if-∧ : ∀ b → (if b ∧ c then x else y) ≡ (if b then (if c then x else y) else y)
  if-∨ : ∀ b → (if b ∨ c then x else y) ≡ (if b then x else (if c then x else y))
  if-xor : ∀ b → (if b xor c then x else y) ≡ (if b then (if c then y else x) else (if c then x else y))
  if-cong : b ≡ c → (if b then x else y) ≡ (if c then x else y)
  if-cong-then : ∀ b → x ≡ z → (if b then x else y) ≡ (if b then z else y)
  if-cong-else : ∀ b → y ≡ z → (if b then x else y) ≡ (if b then x else z)
  if-cong₂ : ∀ b → x ≡ z → y ≡ w → (if b then x else y) ≡ (if b then z else w)
  ```

* In `Data.Fin.Base`:
  ```agda
  _≰_ : Rel (Fin n) 0ℓ
  _≮_ : Rel (Fin n) 0ℓ
  lower : ∀ (i : Fin m) → .(toℕ i ℕ.< n) → Fin n
  ```

* In `Data.Fin.Permutation`:
  ```agda
  cast-id : .(m ≡ n) → Permutation m n
  swap : Permutation m n → Permutation (2+ m) (2+ n)
  ```

* In `Data.Fin.Properties`:
  ```agda
  cast-involutive       : .(eq₁ : m ≡ n) .(eq₂ : n ≡ m) → ∀ k → cast eq₁ (cast eq₂ k) ≡ k
  inject!-injective     : Injective _≡_ _≡_ inject!
  inject!-<             : (k : Fin′ i) → inject! k < i
  lower-injective       : lower i i<n ≡ lower j j<n → i ≡ j
  injective⇒existsPivot : ∀ (f : Fin n → Fin m) → Injective _≡_ _≡_ f → ∀ (i : Fin n) → ∃ λ j → j ≤ i × i ≤ f j
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
  length-++-sucˡ : ∀ (x : A) (xs ys : List A) → length (x ∷ xs ++ ys) ≡ suc (length (xs ++ ys))
  length-++-sucʳ : ∀ (xs : List A) (y : A) (ys : List A) → length (xs ++ y ∷ ys) ≡ suc (length (xs ++ ys))
  length-++-comm : ∀ (xs ys : List A) → length (xs ++ ys) ≡ length (ys ++ xs)
  length-++-≤ˡ : ∀ (xs : List A) → length xs ≤ length (xs ++ ys)
  length-++-≤ʳ : ∀ (ys : List A) → length ys ≤ length (xs ++ ys)
  map-applyUpTo : ∀ (f : ℕ → A) (g : A → B) n → map g (applyUpTo f n) ≡ applyUpTo (g ∘ f) n
  map-applyDownFrom : ∀ (f : ℕ → A) (g : A → B) n → map g (applyDownFrom f n) ≡ applyDownFrom (g ∘ f) n
  map-upTo : ∀ (f : ℕ → A) n → map f (upTo n) ≡ applyUpTo f n
  map-downFrom : ∀ (f : ℕ → A) n → map f (downFrom n) ≡ applyDownFrom f n
  ```

* In `Data.List.Relation.Binary.Permutation.Homogeneous`:
  ```agda
  onIndices : Permutation R xs ys → Fin.Permutation (length xs) (length ys)
  ```

* In `Data.List.Relation.Binary.Permutation.Propositional`:
  ```agda
  ↭⇒↭ₛ′ : IsEquivalence _≈_ → _↭_ ⇒ _↭ₛ′_
  ```

* In `Data.List.Relation.Binary.Permutation.Setoid.Properties`:
  ```agda
  xs↭ys⇒|xs|≡|ys| : xs ↭ ys → length xs ≡ length ys
  ¬x∷xs↭[] : ¬ (x ∷ xs ↭ [])
  onIndices-lookup : ∀ i → lookup xs i ≈ lookup ys (Inverse.to (onIndices xs↭ys) i)
  ```

* In `Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  filter-↭ : ∀ (P? : Pred.Decidable P) → xs ↭ ys → filter P? xs ↭ filter P? ys
        ```

* In `Data.List.Relation.Binary.Pointwise.Properties`:
  ```agda
  lookup-cast : Pointwise R xs ys → .(∣xs∣≡∣ys∣ : length xs ≡ length ys) → ∀ i → R (lookup xs i) (lookup ys (cast ∣xs∣≡∣ys∣ i))
  ```

* In `Data.List.NonEmpty.Properties`:
  ```agda
  ∷→∷⁺ : (x List.∷ xs) ≡ (y List.∷ ys) →
         (x List⁺.∷ xs) ≡ (y List⁺.∷ ys)
  ∷⁺→∷ : (x List⁺.∷ xs) ≡ (y List⁺.∷ ys) →
         (x List.∷ xs) ≡ (y List.∷ ys)
  length-⁺++⁺ : (xs ys : List⁺ A) → length (xs ⁺++⁺ ys) ≡ length xs + length ys
  length-⁺++⁺-comm : ∀ (xs ys : List⁺ A) → length (xs ⁺++⁺ ys) ≡ length (ys ⁺++⁺ xs)
  length-⁺++⁺-≤ˡ : (xs ys : List⁺ A) → length xs ≤ length (xs ⁺++⁺ ys)
  length-⁺++⁺-≤ʳ : (xs ys : List⁺ A) → length ys ≤ length (xs ⁺++⁺ ys)
  map-⁺++⁺ : ∀ (f : A → B) xs ys → map f (xs ⁺++⁺ ys) ≡ map f xs ⁺++⁺ map f ys
  ⁺++⁺-assoc : Associative _⁺++⁺_
  ⁺++⁺-cancelˡ : LeftCancellative _⁺++⁺_
  ⁺++⁺-cancelʳ : RightCancellative _⁺++⁺_
  ⁺++⁺-cancel : Cancellative _⁺++⁺_
  map-id : map id ≗ id {A = List⁺ A}
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

* In `Data.Vec.Properties`:
  ```agda
  toList-injective : ∀ {m n} → .(m=n : m ≡ n) → (xs : Vec A m) (ys : Vec A n) → toList xs ≡ toList ys → xs ≈[ m=n ] ys

  toList-∷ʳ : ∀ x (xs : Vec A n) → toList (xs ∷ʳ x) ≡ toList xs List.++ List.[ x ]

  fromList-reverse : (xs : List A) → (fromList (List.reverse xs)) ≈[ List.length-reverse xs ] reverse (fromList xs)

  fromList∘toList : ∀  (xs : Vec A n) → fromList (toList xs) ≈[ length-toList xs ] xs
  ```

* In `Data.Product.Nary.NonDependent`:
  ```agda
  HomoProduct′ n f = Product n (stabulate n (const _) f)
  HomoProduct  n A = HomoProduct′ n (const A)
  ```

* In `Data.Vec.Relation.Binary.Pointwise.Inductive`:
  ```agda
  zipWith-assoc : Associative _∼_ f → Associative (Pointwise _∼_) (zipWith {n = n} f)
  zipWith-identityˡ: LeftIdentity _∼_ e f → LeftIdentity (Pointwise _∼_) (replicate n e) (zipWith f)
  zipWith-identityʳ: RightIdentity _∼_ e f → RightIdentity (Pointwise _∼_) (replicate n e) (zipWith f)
  zipWith-comm : Commutative _∼_ f → Commutative (Pointwise _∼_) (zipWith {n = n} f)
  zipWith-cong : Congruent₂ _∼_ f → Pointwise _∼_ ws xs → Pointwise _∼_ ys zs → Pointwise _∼_ (zipWith f ws ys) (zipWith f xs zs)
  ```

* In `Function.Nary.NonDependent.Base`:
  ```agda
  lconst l n = ⨆ l (lreplicate l n)
  stabulate : ∀ n → (f : Fin n → Level) → (g : (i : Fin n) → Set (f i)) → Sets n (ltabulate n f)
  sreplicate : ∀ n → Set a → Sets n (lreplicate n a)
  ```

* In `Relation.Binary.Consequences`:
  ```agda
  mono₂⇒monoˡ : Reflexive ≤₁ → Monotonic₂ ≤₁ ≤₂ ≤₃ f → LeftMonotonic ≤₂ ≤₃ f
  mono₂⇒monoˡ : Reflexive ≤₂ → Monotonic₂ ≤₁ ≤₂ ≤₃ f → RightMonotonic ≤₁ ≤₃ f
  monoˡ∧monoʳ⇒mono₂ : Transitive ≤₃ →
                      LeftMonotonic ≤₂ ≤₃ f → RightMonotonic ≤₁ ≤₃ f →
                      Monotonic₂ ≤₁ ≤₂ ≤₃ f
  ```

* In `Relation.Binary.Construct.Add.Infimum.Strict`:
  ```agda
  <₋-accessible-⊥₋ : Acc _<₋_ ⊥₋
  <₋-accessible[_] : Acc _<_ x → Acc _<₋_ [ x ]
  <₋-wellFounded   : WellFounded _<_ → WellFounded _<₋_
  ```

* In `Relation.Binary.Definitions`:
  ```agda
  LeftMonotonic  : Rel B ℓ₁ → Rel C ℓ₂ → (A → B → C) → Set _
  RightMonotonic : Rel A ℓ₁ → Rel C ℓ₂ → (A → B → C) → Set _
  ```

* In `Relation.Nullary.Decidable`:
  ```agda
  dec-yes-recompute : (a? : Dec A) → .(a : A) → a? ≡ yes (recompute a? a)
  ```

* In `Relation.Nullary.Decidable.Core`:
  ```agda
  ⊤-dec : Dec {a} ⊤
  ⊥-dec : Dec {a} ⊥
  recompute-irrelevant-id : (a? : Decidable A) → Irrelevant A →
                            (a : A) → recompute a? a ≡ a
  ```

* In `Relation.Unary`:
  ```agda
  _⊥_ _⊥′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
  ```

* In `Relation.Unary.Properties`:
  ```agda
  ≬-symmetric : Sym _≬_ _≬_
  ⊥-symmetric : Sym _⊥_ _⊥_
  ≬-sym : Symmetric _≬_
  ⊥-sym : Symmetric _⊥_
  ≬⇒¬⊥ : _≬_ ⇒  (¬_ ∘₂ _⊥_)
  ⊥⇒¬≬ : _⊥_ ⇒  (¬_ ∘₂ _≬_)

* In `Relation.Nullary.Negation.Core`:
  ```agda
  contra-diagonal : (A → ¬ A) → ¬ A
  ```

* In `Relation.Nullary.Reflects`:
  ```agda
  ⊤-reflects : Reflects (⊤ {a}) true
  ⊥-reflects : Reflects (⊥ {a}) false
  ```

* In `Data.List.Relation.Unary.AllPairs.Properties`:
  ```agda
  map⁻ : AllPairs R (map f xs) → AllPairs (R on f) xs
  ```

* In `Data.List.Relation.Unary.Linked`:
  ```agda
  lookup : Transitive R → Linked R xs → Connected R (just x) (head xs) → ∀ i → R x (List.lookup xs i)
  ```

* In `Data.List.Relation.Unary.Unique.Setoid.Properties`:
  ```agda
  map⁻ : Congruent _≈₁_ _≈₂_ f → Unique R (map f xs) → Unique S xs
  ```

* In `Data.List.Relation.Unary.Unique.Propositional.Properties`:
  ```agda
  map⁻ : Unique (map f xs) → Unique xs
  ```

* In `Data.List.Relation.Unary.Sorted.TotalOrder.Properties`:
  ```agda
  lookup-mono-≤ : Sorted xs → i Fin.≤ j → lookup xs i ≤ lookup xs j
  ↗↭↗⇒≋         : Sorted xs → Sorted ys → xs ↭ ys → xs ≋ ys
  ```

* In `Data.List.Sort.Base`:
  ```agda
  SortingAlgorithm.sort-↭ₛ : ∀ xs → sort xs Setoid.↭ xs
  ```
