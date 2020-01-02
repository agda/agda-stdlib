Version 1.3-dev
===============

The library has been tested using Agda version 2.6.0.1.

Highlights
----------

Bug-fixes
---------

Changed the definition of `_⊓_` for `Codata.Conat`; it was mistakenly using
`_⊔_` in a recursive call.

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

* In `Codata.Colist`, replaced all the uses of `Data.BoundedVec` with the more
  up to date `Data.Vec.Bounded`.

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

* Added new module:
  ```agda
  Codata.Cowriter.Bisimilarity
  ```

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

* Made `RawFunctor`,  `RawApplicative` and `IFun` more level polymorphic
  (in `Category.Functor`, `Category.Applicative` and
  `Category.Applicative.Indexed`
  respectively).

Other minor additions
---------------------

* Added new proofs to `Algebra.Properties.Group`:
  ```agda
  ⁻¹-injective   : x ⁻¹ ≈ y ⁻¹ → x ≈ y
  ⁻¹-anti-homo-∙ : (x ∙ y) ⁻¹ ≈ y ⁻¹ ∙ x ⁻¹
  ```

* Added new functions to `Codata.Colist`:
  ```agda
  drop   : ℕ → Colist A ∞ → Colist A ∞
  concat : Colist (List⁺ A) i → Colist A i
  ```

* Added new definitions to `Codata.Colist.Bisimilarity`:
  ```agda
  fromEq        : as ≡ bs → i ⊢ as ≈ bs
  isEquivalence : IsEquivalence R → IsEquivalence (Bisim R i)
  setoid        : Setoid a r → Size → Setoid a (a ⊔ r)
  module ≈-Reasoning

  ++⁺  : Pointwise R as bs → Bisim R i xs ys → Bisim R i (fromList as ++ xs) (fromList bs ++ ys)
  ⁺++⁺ : Pointwise R (toList as) (toList bs) → Thunk^R (Bisim R) i xs ys → Bisim R i (as ⁺++ xs) (bs ⁺++ ys)
  ```

* Added new proofs to `Codata.Colist.Properties`:
  ```agda
  fromCowriter∘toCowriter≗id : i ⊢ fromCowriter (toCowriter as) ≈ as
  length-∷                   : i ⊢ length (a ∷ as) ≈ 1 ℕ+ length (as .force)
  length-replicate           : i ⊢ length (replicate n a) ≈ n
  length-++                  : i ⊢ length (as ++ bs) ≈ length as + length bs
  length-map                 : i ⊢ length (map f as) ≈ length as
  length-scanl               : i ⊢ length (scanl c n as) ≈ 1 ℕ+ length as
  replicate-+                : i ⊢ replicate (m + n) a ≈ replicate m a ++ replicate n a
  map-replicate              : i ⊢ map f (replicate n a) ≈ replicate n (f a)
  lookup-replicate           : All (a ≡_) (lookup k (replicate n a))
  map-unfold                 : i ⊢ map f (unfold alg a) ≈ unfold (Maybe.map (Prod.map₂ f) ∘ alg) a
  unfold-nothing             : alg a ≡ nothing → unfold alg a ≡ []
  unfold-just                : alg a ≡ just (a′ , b) → i ⊢ unfold alg a ≈ b ∷ λ where .force → unfold alg a′
  scanl-unfold               : i ⊢ scanl cons nil (unfold alg a) ≈ nil ∷ (λ where .force → unfold alg′ (a , nil))
  map-alignWith              : i ⊢ map f (alignWith al as bs) ≈ alignWith (f ∘ al) as bs
  length-alignWith           : i ⊢ length (alignWith al as bs) ≈ length as ⊔ length bs
  map-zipWith                : i ⊢ map f (zipWith zp as bs) ≈ zipWith (λ a → f ∘ zp a) as bs
  length-zipWith             : i ⊢ length (zipWith zp as bs) ≈ length as ⊓ length bs
  drop-nil                   : i ⊢ drop {A = A} m [] ≈ []
  drop-drop-fusion           : i ⊢ drop n (drop m as) ≈ drop (m ℕ.+ n) as
  map-drop                   : i ⊢ map f (drop m as) ≈ drop m (map f as)
  length-drop                : i ⊢ length (drop m as) ≈ length as ∸ m
  length-cotake              : i ⊢ length (cotake n as) ≈ n
  map-cotake                 : i ⊢ map f (cotake n as) ≈ cotake n (Stream.map f as)
  drop-fromList-++-identity  : drop (length as) (fromList as ++ bs) ≡ bs
  drop-fromList-++-≤         : m ≤ length as → drop m (fromList as ++ bs) ≡ fromList (drop m as) ++ bs
  drop-fromList-++-≥         : m ≥ length as → drop m (fromList as ++ bs) ≡ drop (m ∸ length as) bs
  drop-⁺++-identity          : drop (length as) (as ⁺++ bs) ≡ bs .force
  map-chunksOf               : i ⊢ map (map f) (map f) (chunksOf n as) ≈ chunksOf n (map f as)
  fromList-++                : i ⊢ fromList (as ++ bs) ≈ fromList as ++ fromList bs
  fromList-scanl             : i ⊢ scanl c n (fromList as) ≈ fromList (scanl c n as)
  map-fromList               : i ⊢ map f (fromList as) ≈ fromList (map f as)
  length-fromList            : i co⊢ length (fromList as) ≈ fromℕ (length as)
  fromStream-++              : i ⊢ fromStream (as ++ bs) ≈ fromList as ++ fromStream bs
  fromStream-⁺++             : i ⊢ fromStream (as ⁺++ bs) ≈ fromList⁺ as ++ fromStream (bs .force)
  fromStream-concat          : i ⊢ concat (fromStream ass) ≈ fromStream (concat ass)
  fromStream-scanl           : i ⊢ scanl c n (fromStream as) ≈ fromStream (scanl c n as)
  map-fromStream             : i ⊢ map f (fromStream as) ≈ fromStream (map f as)
  ```

* Added new definitions to `Codata.Conat.Bisimilarity`:
  ```agda
  isEquivalence : IsEquivalence (i ⊢_≈_)
  setoid        : Size → Setoid 0ℓ 0ℓ
  module ≈-Reasoning
  ```

* Added new proof to `Codata.Conat.Properties`:
  ```agda
  0∸m≈0 : ∀ m → i ⊢ zero ∸ m ≈ zero
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

* Added new proofs to `Data.Maybe.Properties`:
  ```agda
  map-nothing : ma ≡ nothing → map f ma ≡ nothing
  map-just    : ma ≡ just a → map f ma ≡ just (f a)
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
