Version 1.3-dev
===============

The library has been tested using Agda version 2.6.0.1.

Highlights
----------

Bug-fixes
---------

* The incorrectly named proof `p⊆q⇒∣p∣<∣q∣ : p ⊆ q → ∣ p ∣ ≤ ∣ q ∣` in
  `Data.Fin.Subset.Properties` now has the correct name `p⊆q⇒∣p∣≤∣q∣`.

* Changed the definition of `_⊓_` for `Codata.Conat`; it was mistakenly using
  `_⊔_` in a recursive call.

* Changed the type of `max≈v⁺` in `Data.List.Extrema`; it was mistakenly talking
  about `min` rather than `max`.

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

* The fixity level of `Data.List.Base`'s `_∷ʳ_` was changed from 5 to 6.
  This means that `x ∷ xs ∷ʳ y` and `x ++ xs ∷ʳ y` are not ambiguous
  anymore: they both are parenthesised to the right (the more efficient
  variant).

* Moved module `README.Text` to `README.Text.Printf`.

* The following record definitions in `Algebra.Structures` have been changed.

  - `IsCommutativeMonoid`
  - `IsCommutativeSemiring`
  - `IsRing`

  In all of these cases, the change has been to give each of these structures
  access to *all* of the fields of structures below (weaker) in the hierarchy.
  For example, consider `IsCommutativeMonoid`. The old definition effectively
  required the following fields.

  - Associativity
  - Left identity
  - Commutativity

  The new definition also requires:

  - Right identity.

  The justification for not including a right identity proof was that, given
  left identity and commutativity, right identity can be proven. However,
  omitting the right identity proof caused problems:

  1. It made the definition longer and more complex, as less code was reused.
  2. The forgetful map turning a commutative monoid into a monoid was not a
     retraction of all maps which augment a monoid with commutativity. To see
     that the forgetful map was not a retraction, notice that the augmentation
     must have discarded the right identity proof as there was no field for it
     in `IsCommutativeMonoid`.
  3. There was no easy way to give only the right identity proof, and have
     the left identity proof be generically derived.

  Point 2, and in particular the fact that it did not hold definitionally,
  caused problems when indexing over monoids and commutative monoids and
  requiring some compatibility between the two indexings.

  With the new definition, we address point 3 and recover the convenience of
  the old definition simultaneously. We do this by introducing *biased*
  structures, found in `Algebra.Structures.Biased`. In particular, one can
  generally convert old instances of `IsCommutativeMonoid` to new instances
  using the `IsCommutativeMonoidˡ` biased structure. This is introduced by
  the function `isCommutativeMonoidˡ`, so old instances can be converted as
  follows.

  ```agda
  --    Add this part:  ↓----↓----↓----↓----↓
  isCommutativeMonoid = isCommutativeMonoidˡ record
    { isSemigroup = ...  -- Everything
    ; identityˡ   = ...  -- else is
    ; comm        = ...  -- the same.
    }
  ```

  For `IsCommutativeSemiring`, we have `IsCommutativeSemiringˡ`, and for
  `IsRing`, we have `IsRingWithoutAnnihilatingZero`.

* In `Codata.Colist`, replaced all the uses of `Data.BoundedVec` with the more
  up to date `Data.Vec.Bounded`.

Deprecated names
----------------

The following deprecations have occurred as part of a drive to improve
consistency across the library. The deprecated names still exist and
therefore all existing code should still work, however use of the new
names is encouraged. Although not anticipated any time soon, they may
eventually be removed in some future release of the library. Automated
warnings are attached to all deprecated names to discourage their use.

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  Any¬→¬All  ↦  Any¬⇒¬All
  ```

Other major additions
---------------------

* Added new modules:
  ```agda
  Codata.Cowriter.Bisimilarity

  Data.Erased
  Data.Product.Relation.Unary.All
  Data.Refinement
  Data.Refinement.Relation.Unary.All
  Data.Tree.Binary
  Data.Tree.Binary.Properties
  Data.Tree.Binary.Relation.Unary.All
  Data.Tree.Binary.Relation.Unary.All.Properties
  Data.Tree.Rose
  Data.Tree.Rose.Properties

  Text.Pretty.Core
  Text.Pretty
  Text.Tabular.Base
  Text.Tabular.List
  Text.Tabular.Vec
  Text.Tree.Linear

  README.Text.Pretty
  README.Text.Tabular
  README.Text.Tree
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

* Standardised the `Eq` modules in structures and bundles in `Relation.Binary` hierarchy.
  - `IsDecTotalOrder.Eq` now exports `isDecPartialOrder`.
  - `DecSetoid.Eq` now exports `partialSetoid` and `_≉_`.
  - `Poset.Eq` and `TotalOrder.Eq` now export `setoid`.
  - `DecTotalOrder.Eq` and `StrictTotalOrder.Eq` now export `decSetoid`.
  - `DecTotalOrder.decSetoid` is now deprecated in favour of the above `DecTotalOrder.Eq.decSetoid`.

Other minor additions
---------------------

* Added new definition to `Algebra.Definitions`:
  ```agda
  Interchangable _∘_ _∙_ = ∀ w x y z → ((w ∙ x) ∘ (y ∙ z)) ≈ ((w ∘ y) ∙ (x ∘ z))
  ```

* Added new proofs to `Algebra.Properties.Group`:
  ```agda
  ⁻¹-injective   : x ⁻¹ ≈ y ⁻¹ → x ≈ y
  ⁻¹-anti-homo-∙ : (x ∙ y) ⁻¹ ≈ y ⁻¹ ∙ x ⁻¹
  ```

* Made `RawFunctor`,  `RawApplicative` and `IFun` more level polymorphic
  (in `Category.Functor`, `Category.Applicative` and
  `Category.Applicative.Indexed`
  respectively).

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

* Added new properties to `Data.Fin.Properties`:
  ```agda
  lift-injective : (∀ {x y} → f x ≡ f y → x ≡ y) → ∀ k {x y} → lift k f x ≡ lift k f y → x ≡ y
  ```

* Added new function to `Data.Difference.List`:
  ```agda
  _∷ʳ_ : DiffList A → A → DiffList A
  ```

* Added new properties to `Data.Fin.Subset`:
  ```agda
  _⊂_ : Subset n → Subset n → Set
  _⊄_ : Subset n → Subset n → Set
  ```

* Added new proofs to `Data.Fin.Subset.Properties`:
  ```agda
  s⊆s           : p ⊆ q → s ∷ p ⊆ s ∷ q
  ∣p∣≡n⇒p≡⊤     : ∣ p ∣ ≡ n → p ≡ ⊤

  p∪∁p≡⊤        : p ∪ ∁ p ≡ ⊤
  ∣∁p∣≡n∸∣p∣    : ∣ ∁ p ∣ ≡ n ∸ ∣ p ∣
  x∈p⇒x∉∁p      : x ∈ p → x ∉ ∁ p
  x∈∁p⇒x∉p      : x ∈ ∁ p → x ∉ p
  x∉∁p⇒x∈p      : x ∉ ∁ p → x ∈ p
  x∉p⇒x∈∁p      : x ∉ p → x ∈ ∁ p

  x≢y⇒x∉⁅y⁆     : x ≢ y → x ∉ ⁅ y ⁆
  x∉⁅y⁆⇒x≢y     : x ∉ ⁅ y ⁆ → x ≢ y

  ∣p∩q∣≤∣p∣     : ∣ p ∩ q ∣ ≤ ∣ p ∣
  ∣p∩q∣≤∣q∣     : ∣ p ∩ q ∣ ≤ ∣ q ∣
  ∣p∩q∣≤∣p∣⊓∣q∣ : ∣ p ∩ q ∣ ≤ ∣ p ∣ ⊓ ∣ q ∣
  ∣p∣≤∣p∪q∣     : ∣ p ∣ ≤ ∣ p ∪ q ∣
  ∣q∣≤∣p∪q∣     : ∣ q ∣ ≤ ∣ p ∪ q ∣
  ∣p∣⊔∣q∣≤∣p∪q∣ : ∣ p ∣ ⊔ ∣ q ∣ ≤ ∣ p ∪ q ∣
  ```

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

* Added new functions to `Data.List.Base`:
  ```agda
  _?∷_  : Maybe A → List A → List A
  _∷ʳ?_ : List A → Maybe A → List A
  ```

* Added new properties to `Data.Nat.Properties`:
  ```
  ⌊n/2⌋≤⌈n/2⌉   : ⌊ n /2⌋ ≤ ⌈ n /2⌉
  ⌊n/2⌋+⌈n/2⌉≡n : ⌊ n /2⌋ + ⌈ n /2⌉ ≡ n
  ```

* Added new functions to `Data.String.Base`:
  ```agda
  padLeft    : Char → ℕ → String → String
  padRight   : Char → ℕ → String → String
  padBoth    : Char → Char → ℕ → String → String

  data Alignment : Set where Left Center Right : Alignment
  fromAlignment  : Alignment → ℕ → String → String

  rectangle  : Vec (ℕ → String → String) n → Vec String n → Vec String n
  rectangleˡ : Char → Vec String n → Vec String n
  rectangleʳ : Char → Vec String n → Vec String n
  rectangleᶜ : Char → Char → Vec String n → Vec String n
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

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  ⊔-pres-≤m : n ≤ m → o ≤ m → n ⊔ o ≤ m
  ⊔-pres-<m : n < m → o < m → n ⊔ o < m
  ⊓-pres-m≤ : m ≤ n → m ≤ o → m ≤ n ⊓ o
  ⊓-pres-m< : m < n → m < o → m < n ⊓ o
  ```

* Added new proofs to `Data.String.Unsafe`:
  ```agda
  toList-++        : toList (s ++ t) ≡ toList s ++ toList t
  length-++        : length (s ++ t) ≡ length s + length t
  length-replicate : length (replicate n c) ≡ n
  ```

* Added new functions to `Data.Vec.Base`:
  ```agda
  length    : Vec A n → ℕ
  transpose : Vec (Vec A n) m → Vec (Vec A m) n
  ```

* Added new functions to `Data.Vec.Bounded.Base`:
  ```agda
  take : n → Vec≤ A m → Vec≤ A (n ⊓ m)
  drop : n → Vec≤ A m → Vec≤ A (m ∸ n)

  padLeft   : A → Vec≤ A n → Vec A n
  padRight  : A → Vec≤ A n → Vec A n
  padBoth : ∀ {n} → A → A → Vec≤ A n → Vec A n

  rectangle : List (∃ (Vec≤ A)) → ∃ (List ∘ Vec≤ A)
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

* Added new proofs to `Relation.Binary.Construct.Union`:
  ```agda
  respˡ : L Respectsˡ ≈ → R Respectsˡ ≈ → (L ∪ R) Respectsˡ ≈
  respʳ : L Respectsʳ ≈ → R Respectsʳ ≈ → (L ∪ R) Respectsʳ ≈
  resp₂ : L Respects₂ ≈ → R Respects₂ ≈ → (L ∪ R) Respects₂ ≈
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
