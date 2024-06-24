Version 2.1-dev
===============

The library has been tested using Agda 2.6.4.3.

Highlights
----------

* The size of the dependency graph for many modules has been
  reduced. This may lead to speed ups for first-time loading of some
  modules.

* Added bindings for file handles in `IO.Handle`.

* Added bindings for random number generation in `System.Random`

* Added support for 8-bit words and bytestrings in `Data.Word8` and `Data.ByteString`.

Bug-fixes
---------

* Fixed type of `toList-replicate` in `Data.Vec.Properties`, where `replicate`
  was mistakenly applied to the level of the type `A` instead of the
  variable `x` of type `A`.

* Module `Data.List.Relation.Ternary.Appending.Setoid.Properties` no longer
  incorrectly publicly exports the `Setoid` module under the alias `S`.

* Removed unbound parameter from `length-alignWith`,
  `alignWith-map` and `map-alignWith` in `Data.List.Properties`.

Non-backwards compatible changes
--------------------------------

* The recently added modules and (therefore their contents) in:
  ```agda
  Algebra.Module.Morphism.Structures
  Algebra.Module.Morphism.Construct.Composition
  Algebra.Module.Morphism.Construct.Identity
  ```
  have been changed so they are now parametrized by _raw_ bundles rather
  than lawful bundles.
  This is in line with other modules that define morphisms.
  As a result many of the `Composition` lemmas now take a proof of
  transitivity and the `Identity` lemmas now take a proof of reflexivity.

* The module `IO.Primitive` was moved to `IO.Primitive.Core`.

Minor improvements
------------------

* The definition of the `Pointwise` relational combinator in
  `Data.Product.Relation.Binary.Pointwise.NonDependent.Pointwise`
  has been generalised to take heterogeneous arguments in `REL`.

* The structures `IsSemilattice` and `IsBoundedSemilattice` in
  `Algebra.Lattice.Structures` have been redefined as aliases of
  `IsCommutativeBand` and `IsIdempotentMonoid` in `Algebra.Structures`.

Deprecated modules
------------------

* All modules in the `Data.Word` hierarchy have been deprecated in favour
  of their newly introduced counterparts in `Data.Word64`.

* The module `Data.List.Relation.Binary.Sublist.Propositional.Disjoint`
  has been deprecated in favour of `Data.List.Relation.Binary.Sublist.Propositional.Slice`.

* The modules
  ```
  Function.Endomorphism.Propositional
  Function.Endomorphism.Setoid
  ```
  that used the old `Function` hierarchy have been deprecated in favour of:
  ```
  Function.Endo.Propositional
  Function.Endo.Setoid
  ```

Deprecated names
----------------

* In `Algebra.Properties.Semiring.Mult`:
  ```agda
  1×-identityʳ  ↦  ×-homo-1
  ```

* In `Algebra.Structures.IsGroup`:
  ```agda
  _-_  ↦  _//_
  ```

* In `Algebra.Structures.Biased`:
  ```agda
  IsRing*  ↦  Algebra.Structures.IsRing
  isRing*  ↦  Algebra.Structures.isRing
  ```

* In `Data.Float.Base`:
  ```agda
  toWord ↦ toWord64
  ```

* In `Data.Float.Properties`:
  ```agda
  toWord-injective ↦ toWord64-injective
  ```

* In `Data.List.Base`:
  ```agda
  scanr  ↦  Data.List.Scans.Base.scanr
  scanl  ↦  Data.List.Scans.Base.scanl
  ```

* In `Data.List.Properties`:
  ```agda
  scanr-defn  ↦  Data.List.Scans.Properties.scanr-defn
  scanl-defn  ↦  Data.List.Scans.Properties.scanl-defn
  ```

* In `Data.List.Relation.Unary.All.Properties`:
  ```agda
  map-compose  ↦  map-∘
  ```

* In `Data.Maybe.Base`:
  ```agda
  decToMaybe  ↦  Relation.Nullary.Decidable.Core.dec⇒maybe
  ```

* In `Data.Nat.Base`: the following pattern synonyms and definitions are all
  deprecated in favour of direct pattern matching on `Algebra.Definitions.RawMagma._∣ˡ_._,_`
  ```agda
  pattern less-than-or-equal {k} eq = k , eq
  pattern ≤″-offset k = k , refl
  pattern <″-offset k = k , refl
  s≤″s⁻¹
  ```

* In `Data.Nat.Divisibility.Core`:
  ```agda
  *-pres-∣  ↦  Data.Nat.Divisibility.*-pres-∣
  ```

* In `Data.Sum`:
  ```agda
  fromDec  ↦  Relation.Nullary.Decidable.Core.toSum
  toDec    ↦  Relation.Nullary.Decidable.Core.fromSum
  ```

* In `IO.Base`:
  ```agda
  untilRight  ↦  untilInj₂
  ```

New modules
-----------

* Pointwise lifting of algebraic structures `IsX` and bundles `X` from
  carrier set `C` to function space `A → C`:
  ```
  Algebra.Construct.Pointwise
  ```

* Raw bundles for module-like algebraic structures:
  ```
  Algebra.Module.Bundles.Raw
  ```

* Nagata's construction of the "idealization of a module":
  ```agda
  Algebra.Module.Construct.Idealization
  ```

* The unique morphism from the initial, resp. terminal, algebra:
  ```agda
  Algebra.Morphism.Construct.Initial
  Algebra.Morphism.Construct.Terminal
  ```

* Bytestrings and builders:
  ```agda
  Data.Bytestring.Base
  Data.Bytestring.Builder.Base
  Data.Bytestring.Builder.Primitive
  Data.Bytestring.IO
  Data.Bytestring.IO.Primitive
  Data.Bytestring.Primitive
  ```

* Pointwise and equality relations over indexed containers:
  ```agda
  Data.Container.Indexed.Relation.Binary.Pointwise
  Data.Container.Indexed.Relation.Binary.Pointwise.Properties
  Data.Container.Indexed.Relation.Binary.Equality.Setoid
  ```

* Refactoring of `Data.List.Base.{scanr|scanl}` and their properties:
  ```
  Data.List.Scans.Base
  Data.List.Scans.Properties
  ```

* Various show modules for lists and vector types:
  ```agda
  Data.List.Show
  Data.Vec.Show
  Data.Vec.Bounded.Show
  ```

* Properties of `List` modulo `Setoid` equality (currently only the ([],++) monoid):
  ```
  Data.List.Relation.Binary.Equality.Setoid.Properties
  ```

* Decidability for the subset relation on lists:
  ```agda
  Data.List.Relation.Binary.Subset.DecSetoid (_⊆?_)
  Data.List.Relation.Binary.Subset.DecPropositional
  ```

* Decidability for the disjoint relation on lists:
  ```agda
  Data.List.Relation.Binary.Disjoint.DecSetoid (disjoint?)
  Data.List.Relation.Binary.Disjoint.DecPropositional
  ```

* Prime factorisation of natural numbers.
  ```agda
  Data.Nat.Primality.Factorisation
  ```

* Permutations of vectors as functions:
  ```agda
  Data.Vec.Functional.Relation.Binary.Permutation
  Data.Vec.Functional.Relation.Binary.Permutation.Properties
  ```

* A type of bytes:
  ```agda
  Data.Word8.Primitive
  Data.Word8.Base
  Data.Word8.Literals
  Data.Word8.Show
  ```

* Word64 literals and bit-based functions:
  ```agda
  Data.Word64.Literals
  Data.Word64.Unsafe
  Data.Word64.Show
  ```


* Pointwise equality over functions
  ```
  Function.Relation.Binary.Equality`
  ```

* Consequences of 'infinite descent' for (accessible elements of) well-founded relations:
  ```agda
  Induction.InfiniteDescent
  ```

* New IO primitives to handle buffering
  ```agda
  IO.Primitive.Handle
  IO.Handle
  ```

* Symmetric interior of a binary relation
  ```
  Relation.Binary.Construct.Interior.Symmetric
  ```

* Properties of `Setoid`s with decidable equality relation:
  ```
  Relation.Binary.Properties.DecSetoid
  ```

* Collection of results about recomputability in
  ```agda
  Relation.Nullary.Recomputable
  ```
  with the main definition `Recomputable` exported publicly from `Relation.Nullary`.

* New bindings to random numbers:
  ```agda
  System.Random.Primitive
  System.Random
  ```

Additions to existing modules
-----------------------------

* Added new definitions in `Algebra.Bundles`:
  ```agda
  record SuccessorSet c ℓ : Set (suc (c ⊔ ℓ))
  record CommutativeBand c ℓ : Set (suc (c ⊔ ℓ))
  record IdempotentMonoid c ℓ : Set (suc (c ⊔ ℓ))
  ```
  and additional manifest fields for sub-bundles arising from these in:
  ```agda
  IdempotentCommutativeMonoid
  IdempotentSemiring
  ```

* Added new definition in `Algebra.Bundles.Raw`
  ```agda
  record RawSuccessorSet c ℓ : Set (suc (c ⊔ ℓ))
  ```

* Added new proofs in `Algebra.Construct.Terminal`:
  ```agda
  rawNearSemiring : RawNearSemiring c ℓ
  nearSemiring    : NearSemiring c ℓ
  ```

* In `Algebra.Module.Bundles`, raw bundles are now re-exported and bundles
  consistently expose their raw counterparts.

* Added proofs in `Algebra.Module.Construct.DirectProduct`:
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

* Added proofs in `Algebra.Module.Construct.TensorUnit`:
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

* Added proofs in `Algebra.Module.Construct.Zero`:
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

* Added definitions in `Algebra.Morphism.Structures`:
  ```agda
  record IsSuccessorSetHomomorphism (⟦_⟧ : N₁.Carrier → N₂.Carrier) : Set _
  record IsSuccessorSetMonomorphism (⟦_⟧ : N₁.Carrier → N₂.Carrier) : Set _
  record IsSuccessorSetIsomorphism  (⟦_⟧ : N₁.Carrier →  N₂.Carrier) : Set _

  IsSemigroupHomomorphism : (A → B) → Set _
  IsSemigroupMonomorphism : (A → B) → Set _
  IsSemigroupIsomorphism : (A → B) → Set _
  ```

* Added proof in `Algebra.Properties.AbelianGroup`:
  ```
  ⁻¹-anti-homo‿- : (x - y) ⁻¹ ≈ y - x
  ```

* Added proofs in `Algebra.Properties.Group`:
  ```agda
  isQuasigroup    : IsQuasigroup _∙_ _\\_ _//_
  quasigroup      : Quasigroup _ _
  isLoop          : IsLoop _∙_ _\\_ _//_ ε
  loop            : Loop _ _

  \\-leftDividesˡ  : LeftDividesˡ _∙_ _\\_
  \\-leftDividesʳ  : LeftDividesʳ _∙_ _\\_
  \\-leftDivides   : LeftDivides _∙_ _\\_
  //-rightDividesˡ : RightDividesˡ _∙_ _//_
  //-rightDividesʳ : RightDividesʳ _∙_ _//_
  //-rightDivides  : RightDivides _∙_ _//_

  ⁻¹-selfInverse  : SelfInverse _⁻¹
  x∙y⁻¹≈ε⇒x≈y     : ∀ x y → (x ∙ y ⁻¹) ≈ ε → x ≈ y
  x≈y⇒x∙y⁻¹≈ε     : ∀ {x y} → x ≈ y → (x ∙ y ⁻¹) ≈ ε
  \\≗flip-//⇒comm : (∀ x y → x \\ y ≈ y // x) → Commutative _∙_
  comm⇒\\≗flip-// : Commutative _∙_ → ∀ x y → x \\ y ≈ y // x
  ⁻¹-anti-homo-// : (x // y) ⁻¹ ≈ y // x
  ⁻¹-anti-homo-\\ : (x \\ y) ⁻¹ ≈ y \\ x
  ```

* Added new proofs in `Algebra.Properties.Loop`:
  ```agda
  identityˡ-unique : x ∙ y ≈ y → x ≈ ε
  identityʳ-unique : x ∙ y ≈ x → y ≈ ε
  identity-unique  : Identity x _∙_ → x ≈ ε
  ```

* Added new proofs in `Algebra.Properties.Monoid.Mult`:
  ```agda
  ×-homo-0 : 0 × x ≈ 0#
  ×-homo-1 : 1 × x ≈ x
  ```

* Added new proofs in `Algebra.Properties.Semiring.Mult`:
  ```agda
  ×-homo-0#     : 0 × x ≈ 0# * x
  ×-homo-1#     : 1 × x ≈ 1# * x
  idem-×-homo-* : (_*_ IdempotentOn x) → (m × x) * (n × x) ≈ (m ℕ.* n) × x
  ```

* Added new definitions to `Algebra.Structures`:
  ```agda
  record IsSuccessorSet (suc# : Op₁ A) (zero# : A) : Set _
  record IsCommutativeBand (∙ : Op₂ A) : Set _
  record IsIdempotentMonoid (∙ : Op₂ A) (ε : A) : Set _
  ```

* Added new definitions in `IsGroup` record in `Algebra.Structures`:
  ```agda
  x // y = x ∙ (y ⁻¹)
  x \\ y = (x ⁻¹) ∙ y
  ```

* In `Algebra.Structures` added new proof to `IsCancellativeCommutativeSemiring` record:
  ```agda
  *-cancelʳ-nonZero : AlmostRightCancellative 0# *
  ```

* In `Data.Bool.Show`:
  ```agda
  showBit : Bool → Char
  ```

* In `Data.Container.Indexed.Core`:
  ```agda
  Subtrees o c = (r : Response c) → X (next c r)
  ```

* In `Data.Empty`:
  ```agda
  ⊥-elim-irr  : .⊥ → Whatever
  ```

* In `Data.Fin.Properties`:
  ```agda
  nonZeroIndex : Fin n → ℕ.NonZero n
  ```

* In `Data.Float.Base`:
  ```agda
  _≤_ : Rel Float _
  ```

* In `Data.Integer.Divisibility` introduced `divides` as an explicit pattern synonym
  ```agda
  pattern divides k eq = Data.Nat.Divisibility.divides k eq
  ```

* In `Data.Integer.Properties`:
  ```agda
  ◃-nonZero : .{{_ : ℕ.NonZero n}} → NonZero (s ◃ n)
  sign-*    : .{{NonZero (i * j)}} → sign (i * j) ≡ sign i Sign.* sign j
  i*j≢0     : .{{_ : NonZero i}} .{{_ : NonZero j}} → NonZero (i * j)
  ```

* In `Data.List.Base` added two new functions:
  ```agda
  Inits.tail : List A → List (List A)
  Tails.tail : List A → List (List A)
  ```
  and redefined `inits` and `tails` in terms of them.

* In `Data.List.Membership.Propositional.Properties.Core`:
  ```agda
  find∘∃∈-Any : (p : ∃ λ x → x ∈ xs × P x) → find (∃∈-Any p) ≡ p
  ∃∈-Any∘find : (p : Any P xs) → ∃∈-Any (find p) ≡ p
  ```

* In `Data.List.Membership.Setoid.Properties`:
  ```agda
  reverse⁺ : x ∈ xs → x ∈ reverse xs
  reverse⁻ : x ∈ reverse xs → x ∈ xs
  ```

* In `Data.List.Properties`:
  ```agda
  length-catMaybes       : length (catMaybes xs) ≤ length xs
  applyUpTo-∷ʳ           : applyUpTo f n ∷ʳ f n ≡ applyUpTo f (suc n)
  applyDownFrom-∷ʳ       : applyDownFrom (f ∘ suc) n ∷ʳ f 0 ≡ applyDownFrom f (suc n)
  upTo-∷ʳ                : upTo n ∷ʳ n ≡ upTo (suc n)
  downFrom-∷ʳ            : applyDownFrom suc n ∷ʳ 0 ≡ downFrom (suc n)
  reverse-selfInverse    : SelfInverse {A = List A} _≡_ reverse
  reverse-applyUpTo      : reverse (applyUpTo f n) ≡ applyDownFrom f n
  reverse-upTo           : reverse (upTo n) ≡ downFrom n
  reverse-applyDownFrom  : reverse (applyDownFrom f n) ≡ applyUpTo f n
  reverse-downFrom       : reverse (downFrom n) ≡ upTo n
  mapMaybe-map           : mapMaybe f ∘ map g ≗ mapMaybe (f ∘ g)
  map-mapMaybe           : map g ∘ mapMaybe f ≗ mapMaybe (Maybe.map g ∘ f)
  align-map              : align (map f xs) (map g ys) ≡ map (map f g) (align xs ys)
  zip-map                : zip (map f xs) (map g ys) ≡ map (map f g) (zip xs ys)
  unzipWith-map          : unzipWith f ∘ map g ≗ unzipWith (f ∘ g)
  map-unzipWith          : map (map g) (map h) ∘ unzipWith f ≗ unzipWith (map g h ∘ f)
  unzip-map              : unzip ∘ map (map f g) ≗ map (map f) (map g) ∘ unzip
  splitAt-map            : splitAt n ∘ map f ≗ map (map f) (map f) ∘ splitAt n
  uncons-map             : uncons ∘ map f ≗ map (map f (map f)) ∘ uncons
  last-map               : last ∘ map f ≗ map f ∘ last
  tail-map               : tail ∘ map f ≗ map (map f) ∘ tail
  mapMaybe-cong          : f ≗ g → mapMaybe f ≗ mapMaybe g
  zipWith-cong           : (∀ a b → f a b ≡ g a b) → ∀ as → zipWith f as ≗ zipWith g as
  unzipWith-cong         : f ≗ g → unzipWith f ≗ unzipWith g
  foldl-cong             : (∀ x y → f x y ≡ g x y) → ∀ x → foldl f x ≗ foldl g x
  alignWith-flip         : alignWith f xs ys ≡ alignWith (f ∘ swap) ys xs
  alignWith-comm         : f ∘ swap ≗ f → alignWith f xs ys ≡ alignWith f ys xs
  align-flip             : align xs ys ≡ map swap (align ys xs)
  zip-flip               : zip xs ys ≡ map swap (zip ys xs)
  unzipWith-swap         : unzipWith (swap ∘ f) ≗ swap ∘ unzipWith f
  unzip-swap             : unzip ∘ map swap ≗ swap ∘ unzip
  take-take              : take n (take m xs) ≡ take (n ⊓ m) xs
  take-drop              : take n (drop m xs) ≡ drop m (take (m + n) xs)
  zip-unzip              : uncurry′ zip ∘ unzip ≗ id
  unzipWith-zipWith      : f ∘ uncurry′ g ≗ id →
                           length xs ≡ length ys →
                           unzipWith f (zipWith g xs ys) ≡ (xs , ys)
  unzip-zip              : length xs ≡ length ys → unzip (zip xs ys) ≡ (xs , ys)
  mapMaybe-++            : mapMaybe f (xs ++ ys) ≡ mapMaybe f xs ++ mapMaybe f ys
  unzipWith-++           : unzipWith f (xs ++ ys) ≡
                           zip _++_ _++_ (unzipWith f xs) (unzipWith f ys)
  catMaybes-concatMap    : catMaybes ≗ concatMap fromMaybe
  catMaybes-++           : catMaybes (xs ++ ys) ≡ catMaybes xs ++ catMaybes ys
  map-catMaybes          : map f ∘ catMaybes ≗ catMaybes ∘ map (Maybe.map f)
  Any-catMaybes⁺         : Any (M.Any P) xs → Any P (catMaybes xs)
  mapMaybeIsInj₁∘mapInj₁ : mapMaybe isInj₁ (map inj₁ xs) ≡ xs
  mapMaybeIsInj₁∘mapInj₂ : mapMaybe isInj₁ (map inj₂ xs) ≡ []
  mapMaybeIsInj₂∘mapInj₂ : mapMaybe isInj₂ (map inj₂ xs) ≡ xs
  mapMaybeIsInj₂∘mapInj₁ : mapMaybe isInj₂ (map inj₁ xs) ≡ []
  ```

* In `Data.List.Relation.Binary.Pointwise.Base`:
  ```agda
  unzip : Pointwise (R ; S) ⇒ (Pointwise R ; Pointwise S)
  ```

* In `Data.List.Relation.Binary.Sublist.Setoid`:
  ```agda
  ⊆-upper-bound : ∀ {xs ys zs} (τ : xs ⊆ zs) (σ : ys ⊆ zs) → UpperBound τ σ
  ```

* In `Data.List.Relation.Binary.Sublist.Setoid.Properties`:
  ```agda
  ⊆-trans-idˡ   : (trans-reflˡ : ∀ {x y} (p : x ≈ y) → trans ≈-refl p ≡ p) →
                  (pxs : xs ⊆ ys) → ⊆-trans ⊆-refl pxs ≡ pxs
  ⊆-trans-idʳ   : (trans-reflʳ : ∀ {x y} (p : x ≈ y) → trans p ≈-refl ≡ p) →
                  (pxs : xs ⊆ ys) → ⊆-trans pxs ⊆-refl ≡ pxs
  ⊆-trans-assoc : (≈-assoc : ∀ {w x y z} (p : w ≈ x) (q : x ≈ y) (r : y ≈ z) →
                             trans p (trans q r) ≡ trans (trans p q) r) →
                  (ps : as ⊆ bs) (qs : bs ⊆ cs) (rs : cs ⊆ ds) →
                  ⊆-trans ps (⊆-trans qs rs) ≡ ⊆-trans (⊆-trans ps qs) rs
  ```

* In `Data.List.Relation.Unary.All`:
  ```agda
  universal-U : Universal (All U)
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

* In `Data.List.Relation.Unary.Any.Properties`:
  ```agda
  map-cong : (f g : P ⋐ Q) → (∀ {x} (p : P x) → f p ≡ g p) →
             (p : Any P xs) → Any.map f p ≡ Any.map g p
  ```

* Added new proofs to `Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  product-↭   : product Preserves _↭_ ⟶ _≡_
  catMaybes-↭ : xs ↭ ys → catMaybes xs ↭ catMaybes ys
  mapMaybe-↭  : xs ↭ ys → mapMaybe f xs ↭ mapMaybe f ys
  ```

* Added new proofs to `Data.List.Relation.Binary.Permutation.Setoid.Properties.Maybe`:
  ```agda
  catMaybes-↭ : xs ↭ ys → catMaybes xs ↭ catMaybes ys
  mapMaybe-↭  : xs ↭ ys → mapMaybe f xs ↭ mapMaybe f ys
  ```

* In `Data.List.Relation.Binary.Subset.Setoid.Properties`:
  ```agda
  map⁺ : f Preserves _≈_ ⟶ _≈′_ → as ⊆ bs → map f as ⊆′ map f bs

  reverse-selfAdjoint : as ⊆ reverse bs → reverse as ⊆ bs
  reverse⁺            : as ⊆ bs → reverse as ⊆ reverse bs
  reverse⁻            : reverse as ⊆ reverse bs → as ⊆ bs
  ```

* Added new proofs to `Data.List.Relation.Binary.Sublist.Propositional.Slice`:
  ```agda
  ⊆-upper-bound-is-cospan : (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) → IsCospan (⊆-upper-bound τ₁ τ₂)
  ⊆-upper-bound-cospan    : (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) → Cospan τ₁ τ₂
  ```

* In `Data.List.Relation.Ternary.Appending.Setoid.Properties`:
  ```agda
  through→ : ∃[ xs ] Pointwise _≈_ as xs × Appending xs bs cs →
             ∃[ ys ] Appending as bs ys × Pointwise _≈_ ys cs
  through← : ∃[ ys ] Appending as bs ys × Pointwise _≈_ ys cs →
             ∃[ xs ] Pointwise _≈_ as xs × Appending xs bs cs
  assoc→   : ∃[ xs ] Appending as bs xs × Appending xs cs ds →
             ∃[ ys ] Appending bs cs ys × Appending as ys ds
  ```

* In `Data.List.Relation.Ternary.Appending.Properties`:
  ```agda
  through→ : (R ⇒ (S ; T)) → ((U ; V) ⇒ (W ; T)) →
                 ∃[ xs ] Pointwise U as xs × Appending V R xs bs cs →
                         ∃[ ys ] Appending W S as bs ys × Pointwise T ys cs
  through← : ((R ; S) ⇒ T) → ((U ; S) ⇒ (V ; W)) →
                 ∃[ ys ] Appending U R as bs ys × Pointwise S ys cs →
                         ∃[ xs ] Pointwise V as xs × Appending W T xs bs cs
  assoc→ :   (R ⇒ (S ; T)) → ((U ; V) ⇒ (W ; T)) → ((Y ; V) ⇒ X) →
                     ∃[ xs ] Appending Y U as bs xs × Appending V R xs cs ds →
                         ∃[ ys ] Appending W S bs cs ys × Appending X T as ys ds
  assoc← :   ((S ; T) ⇒ R) → ((W ; T) ⇒ (U ; V)) → (X ⇒ (Y ; V)) →
             ∃[ ys ] Appending W S bs cs ys × Appending X T as ys ds →
                         ∃[ xs ] Appending Y U as bs xs × Appending V R xs cs ds
  ```

* In `Data.List.NonEmpty.Base`:
  ```agda
  inits : List A → List⁺ (List A)
  tails : List A → List⁺ (List A)
  ```

* In `Data.List.NonEmpty.Properties`:
  ```agda
  toList-inits : toList ∘ List⁺.inits ≗ List.inits
  toList-tails : toList ∘ List⁺.tails ≗ List.tails
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

* Added new proofs to `Data.Nat.Primality`:
  ```agda
  rough∧square>⇒prime : .{{NonTrivial n}} → m Rough n → m * m > n → Prime n
  productOfPrimes≢0 : All Prime as → NonZero (product as)
  productOfPrimes≥1 : All Prime as → product as ≥ 1
  ```

* Added new proofs in `Data.Nat.Properties`:
  ```agda
  m≤n+o⇒m∸n≤o    : m ≤ n + o → m ∸ n ≤ o
  m<n+o⇒m∸n<o    : .{{NonZero o}} → m < n + o → m ∸ n < o
  pred-cancel-≤  : pred m ≤ pred n → (m ≡ 1 × n ≡ 0) ⊎ m ≤ n
  pred-cancel-<  : pred m < pred n → m < n
  pred-injective : .{{NonZero m}} → .{{NonZero n}} → pred m ≡ pred n → m ≡ n
  pred-cancel-≡  : pred m ≡ pred n → ((m ≡ 0 × n ≡ 1) ⊎ (m ≡ 1 × n ≡ 0)) ⊎ m ≡ n

  <⇒<″          : _<_ ⇒ _<″_
  m≤n⇒∃[o]m+o≡n : .(m ≤ n) → ∃ λ k → m + k ≡ n
  guarded-∸≗∸   : .(m≤n : m ≤ n) → let k , _ = m≤n⇒∃[o]m+o≡n m≤n in k ≡ n ∸ m
  ```

* Added some very-dependent map and zipWith to `Data.Product`.
  ```agda
  map-Σ : {B : A → Set b} {P : A → Set p} {Q : {x : A} → P x → B x → Set q} →
   (f : (x : A) → B x) → (∀ {x} → (y : P x) → Q y (f x)) →
   ((x , y) : Σ A P) → Σ (B x) (Q y)

  map-Σ′ : {B : A → Set b} {P : Set p} {Q : P → Set q} →
    (f : (x : A) → B x) → ((x : P) → Q x) → ((x , y) : A × P) → B x × Q y

  zipWith : {P : A → Set p} {Q : B → Set q} {R : C → Set r} {S : (x : C) → R x → Set s}
    (_∙_ : A → B → C) → (_∘_ : ∀ {x y} → P x → Q y → R (x ∙ y)) →
    (_*_ : (x : C) → (y : R x) → S x y) →
    ((a , p) : Σ A P) → ((b , q) : Σ B Q) →
        S (a ∙ b) (p ∘ q)
  ```

* In `Data.Rational.Properties`:
  ```agda
  1≢0 : 1ℚ ≢ 0ℚ

  #⇒invertible : p ≢ q → Invertible 1ℚ _*_ (p - q)
  invertible⇒# : Invertible 1ℚ _*_ (p - q) → p ≢ q

  isHeytingCommutativeRing : IsHeytingCommutativeRing _≡_ _≢_ _+_ _*_ -_ 0ℚ 1ℚ
  isHeytingField           : IsHeytingField _≡_ _≢_ _+_ _*_ -_ 0ℚ 1ℚ
  heytingCommutativeRing   : HeytingCommutativeRing 0ℓ 0ℓ 0ℓ
  heytingField             : HeytingField 0ℓ 0ℓ 0ℓ
  ```

* Added new functions in `Data.String.Base`:
  ```agda
  map     : (Char → Char) → String → String
  between : String → String → String → String
  ```

* Added new functions in `Data.Vec.Bounded.Base`:
  ```agda
  isBounded : (as : Vec≤ A n) → Vec≤.length as ≤ n
  toVec     : (as : Vec≤ A n) → Vec A (Vec≤.length as)
  ```

* In `Data.Word64.Base`:
  ```agda
  _≤_ : Rel Word64 zero
  show : Word64 → String
  ```

* In `Function.Bundles`, added `_⟶ₛ_` as a synonym for `Func` that can
  be used infix.

* Re-exported new types and functions in `IO`:
  ```agda
  BufferMode : Set
  noBuffering : BufferMode
  lineBuffering : BufferMode
  blockBuffering : Maybe ℕ → BufferMode
  Handle : Set
  stdin : Handle
  stdout : Handle
  stderr : Handle
  hSetBuffering : Handle → BufferMode → IO ⊤
  hGetBuffering : Handle → IO BufferMode
  hFlush : Handle → IO ⊤
  ```

* Added new functions in `IO.Base`:
  ```agda
  whenInj₂ : E ⊎ A → (A → IO ⊤) → IO ⊤
  forever : IO ⊤ → IO ⊤
  ```

* In `IO.Primitive.Core`:
  ```agda
  _>>_ : IO A → IO B → IO B
  ```

* Added new definition in `Relation.Binary.Construct.Closure.Transitive`
  ```agda
  transitive⁻ : Transitive _∼_ → TransClosure _∼_ ⇒ _∼_
  ```

* Added new proofs in `Relation.Binary.Construct.Composition`:
  ```agda
  transitive⇒≈;≈⊆≈ : Transitive ≈ → (≈ ; ≈) ⇒ ≈
  ```

* Added new definitions in `Relation.Binary.Definitions`
  ```agda
  Stable _∼_ = ∀ x y → Nullary.Stable (x ∼ y)
  Empty  _∼_ = ∀ {x y} → ¬ (x ∼ y)
  ```

* Added new proofs in `Relation.Binary.Properties.Setoid`:
  ```agda
  ≉-irrefl : Irreflexive _≈_ _≉_
  ≈;≈⇒≈ : _≈_ ; _≈_ ⇒ _≈_
  ≈⇒≈;≈ : _≈_ ⇒ _≈_ ; _≈_
  ```

* Added new definitions in `Relation.Nullary`
  ```agda
  Recomputable    : Set _
  WeaklyDecidable : Set _
  ```

* Added new proofs in `Relation.Nullary.Decidable`:
  ```agda
  ⌊⌋-map′ : (a? : Dec A) → ⌊ map′ t f a? ⌋ ≡ ⌊ a? ⌋
  does-⇔  : A ⇔ B → (a? : Dec A) → (b? : Dec B) → does a? ≡ does b?
  does-≡  : (a? b? : Dec A) → does a? ≡ does b?
  ```

* Added new definitions and proofs in `Relation.Nullary.Decidable.Core`:
  ```agda
  dec⇒maybe          : Dec A → Maybe A
  recompute-constant : (a? : Dec A) (p q : A) → recompute a? p ≡ recompute a? q
  toSum              : Dec A → A ⊎ ¬ A
  fromSum            : A ⊎ ¬ A → Dec A
  ```

* Added new definitions in `Relation.Nullary.Negation.Core`:
  ```agda
  contradiction-irr : .A → ¬ A → Whatever
  ```

* Added new definitions in `Relation.Nullary.Reflects`:
  ```agda
  recompute          : Reflects A b → Recomputable A
  recompute-constant : (r : Reflects A b) (p q : A) → recompute r p ≡ recompute r q
  ```

* Added new definitions in `Relation.Unary`:
  ```agda
  Stable          : Pred A ℓ → Set _
  WeaklyDecidable : Pred A ℓ → Set _
  ```

* Added new proofs in `Relation.Nullary.Properties`:
  ```agda
  ≐?     : P ≐ Q → Decidable P → Decidable Q
  does-≐ : P ≐ Q → (P? : Decidable P) → (Q? : Decidable Q) → does ∘ P? ≗ does ∘ Q?
  does-≡ : (P? P?′ : Decidable P) → does ∘ P? ≗ does ∘ P?′
  ```

* Enhancements to `Tactic.Cong` - see `README.Tactic.Cong` for details.
  - Provide a marker function, `⌞_⌟`, for user-guided anti-unification.
  - Improved support for equalities between terms with instance arguments,
    such as terms that contain `_/_` or `_%_`.
