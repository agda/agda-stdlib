Version 1.3-dev
===============

The library has been tested using Agda version 2.6.0.1.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

#### Tweak to definition of `Permutation.refl`

* The definition of `refl` in `Data.List.Relation.Binary.Permutation.Homogeneous/Setoid`
  has been changed from
  ```agda
  refl  : ∀ {xs} → Permutation R xs xs
  ```
  to:
  ```agda
  refl  : ∀ {xs ys} → Pointwise R xs ys → Permutation R xs ys
  ```
  The old definition did not allow for size preserving transformations of permutations
  via pointwise equalities and hence made it difficult to prove termination of complicated
  proofs and or functions over permutations.

* Correspondingly the proofs `isEquivalence` and `setoid` in `Permutation.Homogeneous`
  now take an extra argument that the base relation `R` must be reflexive.

#### Other

* The following lemmas may have breaking changes in their computational
  behaviour.
  - `Data.Fin.Permutation.Components`: `transpose-inverse`
  - `Data.Fin.Properties`: `decFinSubset`, `all?`

  Definitions that are sensitive to the behaviour of these lemmas, rather than
  just their existence, may need to be revised.

Deprecated names
----------------

The following deprecations have occurred as part of a drive to improve consistency
across the library. The deprecated names still exist and therefore all existing code
should still work, however use of the new names is encouraged. Although not anticipated
any time soon, they may eventually be removed in some future release of the library.
Automated warnings are attached to all deprecated names to discourage their use.

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  Any¬→¬All  ↦  Any¬⇒¬All
  ```

Other major additions
---------------------

* Added induction over subsets to `Data.Fin.Subset.Induction`.

* Rewrote definitions branching on a `Dec` value to branch only on the boolean
  `does` field, wherever possible. Furthermore, branching on the `proof` field
  has been made as late as possible, using the `invert` lemma from
  `Relation.Nullary.Reflects`.

  For example, the old definition of `filter` in `Data.List.Base` used the
  `yes` and `no` patterns, which desugared to the following.

  ```agda
  filter : ∀ {P : Pred A p} → Decidable P → List A → List A
  filter P? [] = []
  filter P? (x ∷ xs) with P? x
  ... | false because ofⁿ _ = filter P? xs
  ... |  true because ofʸ _ = x ∷ filter P? xs
  ```

  Because the proofs (`ofⁿ _` and `ofʸ _`) are not giving us any information,
  we do not need to match on them. We end up with the following definition,
  where the `proof` field has been projected away.

  ```agda
  filter : ∀ {P : Pred A p} → Decidable P → List A → List A
  filter P? [] = []
  filter P? (x ∷ xs) with does (P? x)
  ... | false = filter P? xs
  ... | true  = x ∷ filter P? xs
  ```

  Correspondingly, when proving a property of `filter`, we can often make a
  similar change, but sometimes need the proof eventually. The following
  example is adapted from `Data.List.Membership.Setoid.Properties`.

  ```agda
  module _ {c ℓ p} (S : Setoid c ℓ) {P : Pred (Carrier S) p}
           (P? : Decidable P) (resp : P Respects (Setoid._≈_ S)) where

    open Membership S using (_∈_)

    ∈-filter⁺ : ∀ {v xs} → v ∈ xs → P v → v ∈ filter P? xs
    ∈-filter⁺ {xs = x ∷ _} (here v≈x) Pv with P? x
    -- There is no matching on the proof, so we can emit the result without
    -- computing the proof at all.
    ... |  true because   _   = here v≈x
    -- `invert` is used to get the proof just when it is needed.
    ... | false because [¬Px] = contradiction (resp v≈x Pv) (invert [¬Px])
    -- In the remaining cases, we make no use of the proof.
    ∈-filter⁺ {xs = x ∷ _} (there v∈xs) Pv with does (P? x)
    ... | true  = there (∈-filter⁺ v∈xs Pv)
    ... | false = ∈-filter⁺ v∈xs Pv
  ```

Other minor additions
---------------------

* Added new proofs to `Algebra.Properties.Group`:
  ```agda
  ⁻¹-injective   : x ⁻¹ ≈ y ⁻¹ → x ≈ y
  ⁻¹-anti-homo-∙ : (x ∙ y) ⁻¹ ≈ y ⁻¹ ∙ x ⁻¹
  ```

* Added new proofs to `Data.Bool`:
  ```agda
  not-injective : not x ≡ not y → x ≡ y
  ```

* Added new properties to `Data.Fin.Subset`:
  ```agda
  _⊂_ : Subset n → Subset n → Set
  _⊄_ : Subset n → Subset n → Set
  ```

* Added new proofs to `Data.Fin.Subset.Properties`:
  ```agda
  s⊆s : p ⊆ q → s ∷ p ⊆ s ∷ q

  x∈s⇒x∉∁s : x ∈ s → x ∉ ∁ s
  x∈∁s⇒x∉s : x ∈ ∁ s → x ∉ s
  x∉∁s⇒x∈s : x ∉ ∁ s → x ∈ s
  x∉s⇒x∈∁s : x ∉ s → x ∈ ∁ s
  ```

* Added new proofs to `Data.List.Relation.Binary.Equality.Setoid`:
  ```agda
  Any-resp-≋      : P Respects _≈_ → (Any P) Respects _≋_
  All-resp-≋      : P Respects _≈_ → (All P) Respects _≋_
  AllPairs-resp-≋ : R Respects₂ _≈_ → (AllPairs R) Respects _≋_
  Unique-resp-≋   : Unique Respects _≋_
  ```

* Added new proofs to `Data.List.Relation.Binary.Pointwise`:
  ```agda
  Any-resp-Pointwise      : P Respects _∼_ → (Any P) Respects (Pointwise _∼_)
  All-resp-Pointwise      : P Respects _∼_ → (All P) Respects (Pointwise _∼_)
  AllPairs-resp-Pointwise : R Respects₂ _∼_ → (AllPairs R) Respects (Pointwise _∼_)
  ```

* Added new combinators and functions to `Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning`:
  ```agda
  _≋⟨_⟩_  : x ≋ y → y IsRelatedTo z → x IsRelatedTo z
  _≋˘⟨_⟩_ : y ≋ x → y IsRelatedTo z → x IsRelatedTo z

  ↭-prep : xs ↭ ys → x ∷ xs ↭ x ∷ ys
  ↭-swap : xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
  ```

* Added new proofs to `Induction.WellFounded`:
  ```agda
  some-wfRec-irrelevant : Some.wfRec P f x q ≡ Some.wfRec P f x q'
  wfRecBuilder-wfRec    : All.wfRecBuilder P f x y y<x ≡ All.wfRec P f y
  unfold-wfRec          : All.wfRec P f x ≡ f x λ y _ → All.wfRec P f y
  ```

* Added a new proof to `Relation.Nullary.Decidable`:
  ```agda
  isYes≗does : (P? : Dec P) → isYes P? ≡ does P?
  ```

* Added new proofs to `Relation.Binary.Setoid.Properties`:
  ```agda
  ≉-resp₂ : _≉_ Respects₂ _≈_
  ```

* Added new proofs to `Data.Rational.Properties`:
  ```agda
  ↥-* : ↥ (p * q) ℤ.* *-nf p q ≡ ↥ p ℤ.* ↥ q
  ↧-* : ↧ (p * q) ℤ.* *-nf p q ≡ ↧ p ℤ.* ↧ q

  toℚᵘ-homo-*                 : Homomorphic₂ toℚᵘ _*_ ℚᵘ._*_
  toℚᵘ-isMagmaHomomorphism-*  : IsMagmaHomomorphism *-rawMagma ℚᵘ.*-rawMagma toℚᵘ
  toℚᵘ-isMonoidHomomorphism-* : IsMonoidHomomorphism *-rawMonoid ℚᵘ.*-rawMonoid toℚᵘ
  toℚᵘ-isMonoidMonomorphism-* : IsMonoidMonomorphism *-rawMonoid ℚᵘ.*-rawMonoid toℚᵘ

  *-assoc     : Associative _*_
  *-comm      : Commutative _*_
  *-identityˡ : LeftIdentity 1ℚ _*_
  *-identityʳ : RightIdentity 1ℚ _*_
  *-identity  : Identity 1ℚ _*_

  *-isMagma               : IsMagma _*_
  *-isSemigroup           : IsSemigroup _*
  *-1-isMonoid            : IsMonoid _*_ 1ℚ
  *-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1ℚ
  *-rawMagma              : RawMagma 0ℓ 0ℓ
  *-rawMonoid             : RawMonoid 0ℓ 0ℓ
  *-magma                 : Magma 0ℓ 0ℓ
  *-semigroup             : Semigroup 0ℓ 0ℓ
  *-1-monoid              : Monoid 0ℓ 0ℓ
  *-1-commutativeMonoid   : CommutativeMonoid 0ℓ 0ℓ
  ```
