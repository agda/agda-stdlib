Version 1.6-dev
===============

The library has been tested using Agda 2.6.1 and 2.6.1.1.

Highlights
----------

* Drastically reorganised the module hierarchy in the dependency graph of
  the `IO` module so that we may compile a program as simple as hello world
  without pulling upwards of 130 modules.

* First verified implementation of a sorting algorithm (available from `Data.List.Sort`).

Bug-fixes
---------

* Despite being designed for use with non-reflexive relations, the combinators 
  in `Relation.Binary.Reasoning.Base.Partial` required users to provide a proof
  of reflexivity of the relation over the last element in the chain:
  ```agda
  begin 
    x  ⟨ x∼y ⟩
    y  ∎⟨ y∼y ⟩
  ```
  These have now been redefined so that this proof is no longer needed:
  ```agda
  begin 
    x  ⟨ x∼y ⟩
    y  ∎
  ```
  For direct users of `Relation.Binary.Reasoning.PartialSetoid` API this is a 
  backwards compatible change as the `_∎⟨_⟩` combinator has simply been deprecated. For
  users who were building their own reasoning combinators on top of 
  `Relation.Binary.Reasoning.Base.Partial`, they will need to adjust their additional
  combinators to use the new `singleStep`/`multiStep` constructors of `_IsRelatedTo_`.

* The sum operator `_⊎_` in `Data.Container.Indexed.Combinator` was not as universe 
  polymorphic as it should have been. This has been fixed. The old, less universe
  polymorphic variant is still available under the new name `_⊎′_`.
  
* The proof `isEquivalence` in `Function.Properties.(Equivalence/Inverse)` used to be 
  defined in an anonymous module that took two unneccessary `Setoid` arguments:
  ```agda
  module _ (R : Setoid a ℓ₁) (S : Setoid b ℓ₂) where
    isEquivalence : IsEquivalence (Equivalence {a} {b})
  ```
  Their definitions have now been moved out of the anonymous modules so that they no
  longer require these unnecessary arguments.

Non-backwards compatible changes
--------------------------------

* `Data.List.Relation.Binary.Lex.Core` has been thinned to minimise its
  dependencies. The more complex properties (`transitive`, `respects₂`,
  `[]<[]-⇔`, `∷<∷-⇔`, and `decidable`) have been moved to
  `Data.List.Relation.Binary.Lex`.

* `Data.String.Base` has been thinned to minimise its dependencies. The more
  complex functions (`parensIfSpace`, `wordsBy`, `words`, `linesBy`, `lines`,
  `rectangle`, `rectangleˡ`, `rectangleʳ`, `rectangleᶜ`) have been moved to
  `Data.String`.

* The new modules `Relation.Binary.Morphism.(Constant/Identity/Composition)` that
  were added in the last release no longer have module-level arguments. This is in order
  to allow proofs about newly added morphism bundles to be added to these files. This is
  only a breaking change if you were supplying the module arguments upon import, in which
  case you will have to change to supplying them upon application of the proofs.

Deprecated modules
------------------

* The module `Text.Tree.Linear` has been deprecated, and its contents
has been moved to `Data.Tree.Rose.Show`.

Deprecated names
----------------

* In `Data.Nat.Properties`:
  ```agda
  m≤n⇒n⊔m≡n   ↦  m≥n⇒m⊔n≡m
  m≤n⇒n⊓m≡m   ↦  m≥n⇒m⊓n≡n
  n⊔m≡m⇒n≤m   ↦  m⊔n≡n⇒m≤n
  n⊔m≡n⇒m≤n   ↦  m⊔n≡m⇒n≤m
  n≤m⊔n       ↦  m≤n⊔m
  ⊔-least     ↦  ⊔-lub
  ⊓-greatest  ↦  ⊓-glb
  ⊔-pres-≤m   ↦  ⊔-lub
  ⊓-pres-m≤   ↦  ⊓-glb
  ⊔-abs-⊓     ↦  ⊔-absorbs-⊓
  ⊓-abs-⊔     ↦  ⊓-absorbs-⊔
  ∣m+n-m+o∣≡∣n-o| ↦ ∣m+n-m+o∣≡∣n-o∣ -- note final character is a \| rather than a |
  ```

* In `Data.Integer.Properties`:
  ```agda
  m≤n⇒m⊓n≡m  ↦  i≤j⇒i⊓j≡i
  m⊓n≡m⇒m≤n  ↦  i⊓j≡i⇒i≤j
  m≥n⇒m⊓n≡n  ↦  i≥j⇒i⊓j≡j
  m⊓n≡n⇒m≥n  ↦  i⊓j≡j⇒j≤i
  m⊓n≤n      ↦  i⊓j≤j
  m⊓n≤m      ↦  i⊓j≤i
  m≤n⇒m⊔n≡n  ↦  i≤j⇒i⊔j≡j
  m⊔n≡n⇒m≤n  ↦  i⊔j≡j⇒i≤j
  m≥n⇒m⊔n≡m  ↦  i≥j⇒i⊔j≡i
  m⊔n≡m⇒m≥n  ↦  i⊔j≡i⇒j≤i
  m≤m⊔n      ↦  i≤i⊔j
  n≤m⊔n      ↦  i≤j⊔i
  ```

* In `Relation.Binary.Consequences`:
  ```agda
  subst⟶respˡ      ↦ subst⇒respˡ
  subst⟶respʳ      ↦ subst⇒respʳ
  subst⟶resp₂      ↦ subst⇒resp₂
  P-resp⟶¬P-resp   ↦ resp⇒¬-resp
  total⟶refl       ↦ total⇒refl
  total+dec⟶dec    ↦ total∧dec⇒dec
  trans∧irr⟶asym   ↦ trans∧irr⇒asym
  irr∧antisym⟶asym ↦ irr∧antisym⇒asym
  asym⟶antisym     ↦ asym⇒antisym
  asym⟶irr         ↦ asym⇒irr
  tri⟶asym         ↦ tri⇒asym
  tri⟶irr          ↦ tri⇒irr
  tri⟶dec≈         ↦ tri⇒dec≈
  tri⟶dec<         ↦ tri⇒dec<
  trans∧tri⟶respʳ≈ ↦ trans∧tri⇒respʳ
  trans∧tri⟶respˡ≈ ↦ trans∧tri⇒respˡ
  trans∧tri⟶resp≈  ↦ trans∧tri⇒resp
  dec⟶weaklyDec    ↦ dec⇒weaklyDec
  dec⟶recomputable ↦ dec⇒recomputable
  ```

* In `Data.Rational.Properties`:
  ```agda
  neg-mono-<-> ↦ neg-mono-<
  neg-mono-≤-≥ ↦ neg-mono-≤
  ```

New modules
-----------

* Properties of cancellative commutative semirings
  ```
  Algebra.Properties.CancellativeCommutativeSemiring
  ```

* Specifications for min and max operators
  ```
  Algebra.Construct.NaturalChoice.MinOp
  Algebra.Construct.NaturalChoice.MaxOp
  Algebra.Construct.NaturalChoice.MinMaxOp
  ```

* Lexicographic product over algebraic structures
  ```
  Algebra.Construct.LexProduct
  Algebra.Construct.LexProduct.Base
  Algebra.Construct.LexProduct.Inner
  ```

* Properties of sums over semirings
  ```
  Algebra.Properties.Semiring.Sum
  ```

* Sorting algorithms over lists:
  ```
  Data.List.Sort
  Data.List.Sort.Base
  Data.List.Sort.MergeSort
  ```

* Added `Data.Maybe.Relation.Binary.Connected`, a variant of the `Pointwise` 
  relation where `nothing` is also related to `just`.

* Linear congruential pseudo random generators for ℕ.
  /!\ NB: LCGs must not be used for cryptographic applications
  /!\ NB: the example parameters provided are not claimed to be good
  ```
  Data.Nat.PseudoRandom.LCG
  ```

* Factorial, combinations and permutations for ℕ.
  ```
  Data.Nat.Factorial
  Data.Nat.Combinatorics
  Data.Nat.Combinatorics.Base
  ```

* Broke up `Data.List.Relation.Binary.Pointwise` and introduced:
  ```
  Data.List.Relation.Binary.Pointwise.Base
  Data.List.Relation.Binary.Pointwise.Properties
  ```

* Heterogeneous `All` predicate for disjoint sums:
  ```
  Data.Sum.Relation.Unary.All
  ```

* Broke up `Codata.Musical.Colist` into a multitude of modules:
  ```
  Codata.Musical.Colist.Base
  Codata.Musical.Colist.Properties
  Codata.Musical.Colist.Bisimilarity
  Codata.Musical.Colist.Relation.Unary.All
  Codata.Musical.Colist.Relation.Unary.All.Properties
  Codata.Musical.Colist.Relation.Unary.Any
  Codata.Musical.Colist.Relation.Unary.Any.Properties
  ```

* Broke up `IO` into a many smaller modules:
  ```
  IO.Base
  IO.Finite
  IO.Infinite
  ```

* Instantiate a homogeneously indexed bundle at a particular index
  ```
  Relation.Binary.Indexed.Homogeneous.Construct.At
  ```

* Functionality for showing trees:
  ```
  Data.Tree.Rose.Show
  Data.Tree.Binary.Show
  ```

* Bundles for binary relation morphisms
  ```
  Relation.Binary.Morphism.Bundles
  ```

Other minor additions
---------------------

* Added new proofs to `Algebra.Consequences.Setoid`:
  ```agda
  comm+almostCancelˡ⇒almostCancelʳ : AlmostLeftCancellative  e _•_ → AlmostRightCancellative e _•_
  comm+almostCancelʳ⇒almostCancelˡ : AlmostRightCancellative e _•_ → AlmostLeftCancellative  e _•_
  ```

* Added new proofs in `Algebra.Properties.Magma.Divisibility`:
  ```agda
  ∣∣-sym     : Symmetric _∣∣_
  ∣∣-respʳ-≈ : _∣∣_ Respectsʳ _≈_
  ∣∣-respˡ-≈ : _∣∣_ Respectsˡ _≈_
  ∣∣-resp-≈  : _∣∣_ Respects₂ _≈_
  ```

* Added new proofs in `Algebra.Properties.Semigroup.Divisibility`:
  ```agda
  ∣∣-trans : Transitive _∣∣_
  ```

* Added new proofs in `Algebra.Properties.CommutativeSemigroup.Divisibility`:
  ```agda
  x∣y∧z∣x/y⇒xz∣y : ((x/y , _) : x ∣ y) → z ∣ x/y → x ∙ z ∣ y
  x∣y⇒zx∣zy      : x ∣ y → z ∙ x ∣ z ∙ y
  ```

* Added new proofs in `Algebra.Properties.Monoid.Divisibility`:
  ```agda
  ∣∣-refl          : Reflexive _∣∣_
  ∣∣-reflexive     : _≈_ ⇒ _∣∣_
  ∣∣-isEquivalence : IsEquivalence _∣∣_
  ```

* Added new proofs in `Algebra.Properties.CancellativeCommutativeSemiring`:
  ```agda
  xy≈0⇒x≈0∨y≈0 : Decidable _≈_ →  x * y ≈ 0# → x ≈ 0# ⊎ y ≈ 0#
  x≉0∧y≉0⇒xy≉0 : Decidable _≈_ →  x ≉ 0# → y ≉ 0# → x * y ≉ 0#
  xy∣x⇒y∣1     : x ≉ 0# → x * y ∣ x → y ∣ 1#
  ```

* Added new function in `Data.Char.Base`:
  ```agda
  _≈ᵇ_ : (c d : Char) → Bool
  ```

* Added new proofs in `Algebra.Morphism.GroupMonomorphism`:
  ```agda
  ⁻¹-distrib-∙ : ((x ◦ y) ⁻¹₂ ≈₂ (x ⁻¹₂) ◦ (y ⁻¹₂)) → ((x ∙ y) ⁻¹₁ ≈₁ (x ⁻¹₁) ∙ (y ⁻¹₁))
  ```

* Added new proofs in `Algebra.Morphism.RingMonomorphism`:
  ```agda
  neg-distribˡ-* : ((⊝ (x ⊛ y)) ≈₂ ((⊝ x) ⊛ y)) → ((- (x * y)) ≈₁ ((- x) * y))
  neg-distribʳ-* : ((⊝ (x ⊛ y)) ≈₂ (x ⊛ (⊝ y))) → ((- (x * y)) ≈₁ (x * (- y)))
  ```

* Added new function in `Data.List.Base`:
  ```agda
  last : List A → Maybe A
  merge : Decidable R → List A → List A → List A
  ```

* Added new proof in `Data.List.Properties`:
  ```agda
  length-partition : (let (ys , zs) = partition P? xs) → length ys ≤ length xs × length zs ≤ length xs
  ```

* Added new proof in `Data.List.Relation.Binary.Permutation.Setoid.Properties`:
  ```agda
  ↭-shift     : xs ++ [ v ] ++ ys ↭ v ∷ xs ++ ys
  ↭-merge     : merge R? xs ys ↭ xs ++ ys
  ↭-partition : (let ys , zs = partition P? xs) → xs ↭ ys ++ zs
  ```

* Added new operations in `Data.List.Relation.Unary.Linked`:
  ```agda
  head′ : Linked R (x ∷ xs) → Connected R (just x) (head xs)
  _∷′_  : Connected R (just x) (head xs) → Linked R xs → Linked R (x ∷ xs)
  ```

* Generalised the type of operation `tail` in `Data.List.Relation.Unary.Linked`
  from `Linked R (x ∷ y ∷ xs) → Linked R (y ∷ xs)` to `Linked R (x ∷ xs) → Linked R xs`.

* Added new proof in `Data.List.Relation.Unary.Linked.Properties`:
  ```agda
  ++⁺ : Linked R xs → Connected R (last xs) (head ys) → Linked R ys → Linked R (xs ++ ys)
  ```

* Added new proof in `Data.List.Relation.Unary.Sorted.TotalOrder.Properties`:
  ```agda
  ++⁺    : Sorted O xs → Connected _≤_ (last xs) (head ys) → Sorted O ys → Sorted O (xs ++ ys)
  merge⁺ : Sorted O xs → Sorted O ys → Sorted O (merge _≤?_ xs ys)
  ```

* Added new proofs in `Data.List.Relation.Unary.All.Properties`:
  ```agda
  head⁺ : All P xs → Maybe.All P (head xs)
  tail⁺ : All P xs → Maybe.All (All P) (tail xs)
  last⁺ : All P xs → Maybe.All P (last xs)

  uncons⁺ : All P xs → Maybe.All (P ⟨×⟩ All P) (uncons xs)
  uncons⁻ : Maybe.All (P ⟨×⟩ All P) (uncons xs) → All P xs
  unsnoc⁺ : All P xs → Maybe.All (All P ⟨×⟩ P) (unsnoc xs)
  unsnoc⁻ : Maybe.All (All P ⟨×⟩ P) (unsnoc xs) → All P xs

  dropWhile⁺ : (Q? : Decidable Q) → All P xs → All P (dropWhile Q? xs)
  dropWhile⁻ : (P? : Decidable P) → dropWhile P? xs ≡ [] → All P xs
  takeWhile⁺ : (Q? : Decidable Q) → All P xs → All P (takeWhile Q? xs)
  takeWhile⁻ : (P? : Decidable P) → takeWhile P? xs ≡ xs → All P xs

  all-head-dropWhile : (P? : Decidable P) → ∀ xs → Maybe.All (∁ P) (head (dropWhile P? xs))
  all-takeWhile      : (P? : Decidable P) → ∀ xs → All P (takeWhile P? xs)
  ```

* Added new proofs in `Data.Maybe.Relation.Unary.All.Properties`:
  ```agda
  All⇒Connectedˡ : All (R x) y → Connected R (just x) y
  All⇒Connectedʳ : All (λ v → R v y) x → Connected R x (just y
  ```

* Added new proofs to `Data.Nat.DivMod`:
  ```agda
  m<n⇒m/n≡0       : m < n → m / n ≡ 0
  m/n≡1+[m∸n]/n   : m ≥ n → m / n ≡ 1 + (m ∸ n) / n
  m*n/m*o≡n/o     : (m * n) / (m * o) ≡ n / o
  /-cancelʳ-≡     : o ∣ m → o ∣ n → m / o ≡ n / o → m ≡ n
  /-*-interchange : o ∣ m → p ∣ n → (m * n) / (o * p) ≡ m / o * n / p
  ```

* Added new proofs to `Data.Nat.Divisibility`:
  ```agda
  *-pres-∣ : o ∣ m → p ∣ n → o * p ∣ m * n
  m*n∣⇒m∣  : m * n ∣ i → m ∣ i
  m*n∣⇒n∣  : m * n ∣ i → n ∣ i
  ```

* Added new proofs to `Data.Nat.GCD`:
  ```agda
  m/gcd[m,n]≢0 : {m≢0 : Dec.False (m ≟ 0)} → m / gcd m n ≢ 0
  ```

* Added new operations to `Data.Fin.Base`:
  ```agda
  remQuot : remQuot : ∀ k → Fin (n * k) → Fin n × Fin k
  combine : Fin n → Fin k → Fin (n * k)
  ```

* Added new proofs to `Data.Fin.Properties`:
  ```agda
  remQuot-combine : ∀ x y → remQuot k (combine x y) ≡ (x , y)
  combine-remQuot : ∀ k i → uncurry combine (remQuot k i) ≡ i
  *↔× : Fin (m * n) ↔ (Fin m × Fin n)
  ```

* Added new operations to `Data.Fin.Subset`:
  ```
  _─_ : Op₂ (Subset n)
  _-_ : Subset n → Fin n → Subset n
  ```

* Added new proofs to `Data.Fin.Subset.Properties`:
  ```
  s⊂s             : p ⊂ q → s ∷ p ⊂ s ∷ q
  ∣p∣≤∣x∷p∣       : ∣ p ∣ ≤ ∣ x ∷ p ∣

  p─⊥≡p           : p ─ ⊥ ≡ p
  p─⊤≡⊥           : p ─ ⊤ ≡ ⊥
  p─q─r≡p─q∪r     : p ─ q ─ r ≡ p ─ (q ∪ r)
  p─q─r≡p─r─q     : p ─ q ─ r ≡ p ─ r ─ q
  p─q─q≡p─q       : p ─ q ─ q ≡ p ─ q
  p─q⊆p           : p ─ q ⊆ p
  ∣p─q∣≤∣p∣       : ∣ p ─ q ∣ ≤ ∣ p ∣
  p∩q≢∅⇒p─q⊂p     : Nonempty (p ∩ q) → p ─ q ⊂ p
  p∩q≢∅⇒∣p─q∣<∣p∣ : Nonempty (p ∩ q) → ∣ p ─ q ∣ < ∣ p ∣
  x∈p∧x∉q⇒x∈p─q   : x ∈ p → x ∉ q → x ∈ p ─ q

  p─x─y≡p─y─x     : p - x - y ≡ p - y - x
  x∈p⇒p-x⊂p       : x ∈ p → p - x ⊂ p
  x∈p⇒∣p-x∣<∣p∣   : x ∈ p → ∣ p - x ∣ < ∣ p ∣
  x∈p∧x≢y⇒x∈p-y   : x ∈ p → x ≢ y → x ∈ p - y
  ```

* Added new proofs to `Data.Nat.Properties`:
  ```agda
  >⇒≢ : _>_ ⇒ _≢_

  pred[n]≤n : pred n ≤ n

  n>0⇒n≢0 : n > 0 → n ≢ 0
  n<1⇒n≡0 : n < 1 → n ≡ 0
  m<n⇒0<n : m < n → 0 < n

  ≤-isTotalPreorder         : IsTotalPreorder _≡_ _≤_
  ≤-totalPreorder           : TotalPreorder 0ℓ 0ℓ 0ℓ

  ⊔-⊓-absorptive            : Absorptive _⊓_ _
  ⊔-⊓-isLattice             : IsLattice _⊔_ _⊓_
  ⊔-⊓-isDistributiveLattice : IsDistributiveLattice _⊔_ _⊓_

  ⊓-commutativeSemigroup    : CommutativeSemigroup 0ℓ 0ℓ
  ⊔-commutativeSemigroup    : CommutativeSemigroup 0ℓ 0ℓ
  ⊔-0-monoid                : Monoid 0ℓ 0ℓ
  ⊔-⊓-lattice               : Lattice 0ℓ 0ℓ
  ⊔-⊓-distributiveLattice   : DistributiveLattice 0ℓ 0ℓ

  mono-≤-distrib-⊔          : f Preserves _≤_ ⟶ _≤_ → f (x ⊔ y) ≈ f x ⊔ f y
  mono-≤-distrib-⊓          : f Preserves _≤_ ⟶ _≤_ → f (x ⊓ y) ≈ f x ⊓ f y
  antimono-≤-distrib-⊓      : f Preserves _≤_ ⟶ _≥_ → f (x ⊓ y) ≈ f x ⊔ f y
  antimono-≤-distrib-⊔      : f Preserves _≤_ ⟶ _≥_ → f (x ⊔ y) ≈ f x ⊓ f y


  m≤n*m                     : 0 < n → m ≤ n * m
  m≤n⇒n∸m≤n                 : m ≤ n → n ∸ m ≤ n
  m≢0∧n≢0⇒m*n≢0             : m ≢ 0 → n ≢ 0 → m * n ≢ 0
  [m*n]*[o*p]≡[m*o]*[n*p]   : (m * n) * (o * p) ≡ (m * o) * (n * p)
  ```

* Added new definition in `Data.Nat.Base`:
  ```agda
  _≤ᵇ_ : (m n : ℕ) → Bool
  ```

* Added new proof to `Data.Nat.Induction`:
  ```agda
  <-wellFounded-fast : WellFounded _<_
  ```

* Added new relation to `Data.Integer.Base`:
  ```agda
  _≤ᵇ_ : ℤ → ℤ → Bool
  ```

* Added new proofs to `Data.Integer.Properties`:
  ```agda
  ≤-isTotalPreorder         : IsTotalPreorder _≡_ _≤_
  ≤-totalPreorder           : TotalPreorder 0ℓ 0ℓ 0ℓ

  ≤ᵇ⇒≤                      : T (i ≤ᵇ j) → i ≤ j
  ≤⇒≤ᵇ                      : i ≤ j → T (i ≤ᵇ j)

  m*n≡0⇒m≡0∨n≡0             : m * n ≡ 0ℤ → m ≡ 0ℤ ⊎ n ≡ 0ℤ

  ⊓-distribˡ-⊔              : _⊓_ DistributesOverˡ _⊔_
  ⊓-distribʳ-⊔              : _⊓_ DistributesOverʳ _⊔_
  ⊓-distrib-⊔               : _⊓_ DistributesOver  _⊔_
  ⊔-distribˡ-⊓              : _⊔_ DistributesOverˡ _⊓_
  ⊔-distribʳ-⊓              : _⊔_ DistributesOverʳ _⊓_
  ⊔-distrib-⊓               : _⊔_ DistributesOver  _⊓_

  ⊔-⊓-isDistributiveLattice : IsDistributiveLattice _⊔_ _⊓_
  ⊓-⊔-isDistributiveLattice : IsDistributiveLattice _⊓_ _⊔_

  ⊔-⊓-distributiveLattice   : DistributiveLattice _ _
  ⊓-⊔-distributiveLattice   : DistributiveLattice _ _

  ⊓-glb                     : m ≥ o → n ≥ o → m ⊓ n ≥ o
  ⊓-triangulate             : m ⊓ n ⊓ o ≡ (m ⊓ n) ⊓ (n ⊓ o)
  ⊓-mono-≤                  : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊓-monoˡ-≤                 : (_⊓ n) Preserves _≤_ ⟶ _≤_
  ⊓-monoʳ-≤                 : (n ⊓_) Preserves _≤_ ⟶ _≤_

  ⊔-lub                     : m ≤ o → n ≤ o → m ⊔ n ≤ o
  ⊔-triangulate             : m ⊔ n ⊔ o ≡ (m ⊔ n) ⊔ (n ⊔ o)
  ⊔-mono-≤                  : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊔-monoˡ-≤                 : (_⊔ n) Preserves _≤_ ⟶ _≤_
  ⊔-monoʳ-≤                 : (n ⊔_) Preserves _≤_ ⟶ _≤_

  i≤j⇒i⊓k≤j                 : i ≤ j → i ⊓ k ≤ j
  i≤j⇒k⊓i≤j                 : i ≤ j → k ⊓ i ≤ j
  i≤j⊓k⇒i≤j                 : i ≤ j ⊓ k → i ≤ j
  i≤j⊓k⇒i≤k                 : i ≤ j ⊓ k → i ≤ k

  i≤j⇒i≤j⊔k                 : i ≤ j → i ≤ j ⊔ k
  i≤j⇒i≤k⊔j                 : i ≤ j → i ≤ k ⊔ j
  i⊔j≤k⇒i≤k                 : i ⊔ j ≤ k → i ≤ k
  i⊔j≤k⇒j≤k                 : i ⊔ j ≤ k → j ≤ k
  i⊓j≤i⊔j                   : i ⊓ j ≤ i ⊔ j

  +-*-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
  ```

* Added new definitions and proofs to `Relation.Binary.Properties.(Poset/TotalOrder/DecTotalOrder)`:
  ```agda
  _≰_       : Rel A p₃
  ≰-respˡ-≈ : _≰_ Respectsˡ _≈_
  ≰-respʳ-≈ : _≰_ Respectsʳ _≈_
  ```

* Added new proofs to `Data.List.Relation.Binary.Pointwise`:
  ```agda
  foldr⁺  : (R w x → R y z → R (w • y) (x ◦ z)) →
            R e f → Pointwise R xs ys → R (foldr _•_ e xs) (foldr _◦_ f ys)
  lookup⁻ : length xs ≡ length ys →
            (toℕ i ≡ toℕ j → R (lookup xs i) (lookup ys j)) →
            Pointwise R xs ys
  lookup⁺ : (Rxys : Pointwise R xs ys) →
            ∀ i → (let j = cast (Pointwise-length Rxys) i) →
            R (lookup xs i) (lookup ys j)
  ```

* Added new proof to `Data.List.Relation.Unary.All.Properties`:
  ```agda
  all-upTo : All (_< n) (upTo n)
  ```

* Added new proof to `Data.List.Relation.Binary.Equality.Setoid`:
  ```agda
  foldr⁺ : (w ≈ x → y ≈ z → (w • y) ≈ (x ◦ z)) →
           e ≈ f → xs ≋ ys → foldr _•_ e xs ≈ foldr _◦_ f ys
  ```

* Added new proof to `Data.List.Relation.Binary.Subset.Setoid.Properties`:
  ```agda
  xs⊆x∷xs    : xs ⊆ x ∷ xs
  ∷⁺ʳ        : xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
  applyUpTo⁺ : m ≤ n → applyUpTo f m ⊆ applyUpTo f n
  ```

* Added new proof to `Data.List.Relation.Binary.Subset.Propositional.Properties`:
  ```agda
  xs⊆x∷xs    : xs ⊆ x ∷ xs
  ∷⁺ʳ        : xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
  applyUpTo⁺ : m ≤ n → applyUpTo f m ⊆ applyUpTo f n
  ```

* Add new functions to `Data.Rational.Base`:
  ```agda
  _≤ᵇ_ : ℚ → ℚ → Bool
  _⊔_  : (p q : ℚ) → ℚ
  _⊓_  : (p q : ℚ) → ℚ
  ∣_∣  : ℚ → ℚ
  ```

* Add new proofs to `Data.Rational.Properties`:
  ```agda
  mkℚ-cong                   : n₁ ≡ n₂ → d₁ ≡ d₂ → mkℚ n₁ d₁ c₁ ≡ mkℚ n₂ d₂ c₂
  mkℚ+-injective             : mkℚ+ n₁ d₁ c₁ ≡ mkℚ+ n₂ d₂ c₂ → n₁ ≡ n₂ × d₁ ≡ d₂
  mkℚ+-nonNeg                : NonNegative (mkℚ+ n d c)
  mkℚ+-pos                   : NonZero n → Positive (mkℚ+ n d c)

  nonNeg≢neg                 : NonNegative p → Negative q → p ≢ q
  pos⇒nonNeg                 : Positive p → NonNegative p
  neg⇒nonPos                 : Negative p → NonPositive p
  nonNeg∧nonZero⇒pos         : NonNegative p → NonZero p → Positive p

  neg-injective              : - p ≡ - q → p ≡ q
  neg-antimono-<             : -_ Preserves _<_ ⟶ _>_
  neg-antimono-≤             : -_ Preserves _≤_ ⟶ _≥_
  neg-pos                    : Positive p → Negative (- p)

  normalize-cong             : m₁ ≡ m₂ → n₁ ≡ n₂ → normalize m₁ n₁ ≡ normalize m₂ n₂
  normalize-nonNeg           : NonNegative (normalize m n)
  normalize-pos              : NonZero m → Positive (normalize m n)
  normalize-injective-≃      : normalize m c ≡ normalize n d → m ℕ.* d ≡ n ℕ.* c

  /-injective-≃              : ↥ᵘ p / ↧ₙᵘ p ≡ ↥ᵘ q / ↧ₙᵘ q → p ≃ᵘ q

  fromℚᵘ-injective           : Injective _≃ᵘ_ _≡_ fromℚᵘ
  toℚᵘ-fromℚᵘ                : toℚᵘ (fromℚᵘ p) ≃ᵘ p
  fromℚᵘ-cong                : fromℚᵘ Preserves _≃ᵘ_ ⟶ _≡_

  ≤-isTotalPreorder          : IsTotalPreorder _≡_ _≤_
  ≤-totalPreorder            : TotalPreorder 0ℓ 0ℓ 0ℓ

  toℚᵘ-mono-<                : p < q → toℚᵘ p <ᵘ toℚᵘ q
  toℚᵘ-cancel-<              : toℚᵘ p <ᵘ toℚᵘ q → p < q
  toℚᵘ-isOrderHomomorphism-< : IsOrderHomomorphism _≡_ _≃ᵘ_ _<_ _<ᵘ_ toℚᵘ
  toℚᵘ-isOrderMonomorphism-< : IsOrderMonomorphism _≡_ _≃ᵘ_ _<_ _<ᵘ_ toℚᵘ

  ≤ᵇ⇒≤                       : T (p ≤ᵇ q) → p ≤ q
  ≤⇒≤ᵇ                       : p ≤ q → T (p ≤ᵇ q)

  +-mono-≤                   : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  +-monoˡ-≤                  : (_+ r) Preserves _≤_ ⟶ _≤_
  +-monoʳ-≤                  : (_+_ r) Preserves _≤_ ⟶ _≤_
  +-mono-<-≤                 : _+_ Preserves₂ _<_ ⟶ _≤_ ⟶ _<_
  +-mono-<                   : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
  +-monoˡ-<                  : (_+ r) Preserves _<_ ⟶ _<_
  +-monoʳ-<                  : (_+_ r) Preserves _<_ ⟶ _<_

  neg-distrib-+              : - (p + q) ≡ (- p) + (- q)

  *-inverseʳ                 : p * (1/ p) ≡ 1ℚ
  *-inverseˡ                 : (1/ p) * p ≡ 1ℚ

  *-monoʳ-≤-pos              : Positive r    → (_* r) Preserves _≤_ ⟶ _≤_
  *-monoˡ-≤-pos              : Positive r    → (r *_) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤-neg              : Negative r    → (_* r) Preserves _≤_ ⟶ _≥_
  *-monoˡ-≤-neg              : Negative r    → (r *_) Preserves _≤_ ⟶ _≥_
  *-monoʳ-≤-nonNeg           : NonNegative r → (_* r) Preserves _≤_ ⟶ _≤_
  *-monoˡ-≤-nonNeg           : NonNegative r → (r *_) Preserves _≤_ ⟶ _≤_
  *-monoʳ-≤-nonPos           : NonPositive r → (_* r) Preserves _≤_ ⟶ _≥_
  *-monoˡ-≤-nonPos           : NonPositive r → (r *_) Preserves _≤_ ⟶ _≥_
  *-monoˡ-<-pos              : Positive r → (_* r) Preserves _<_ ⟶ _<_
  *-monoʳ-<-pos              : Positive r → (r *_) Preserves _<_ ⟶ _<_
  *-monoˡ-<-neg              : Negative r → (_* r) Preserves _<_ ⟶ _>_
  *-monoʳ-<-neg              : Negative r → (r *_) Preserves _<_ ⟶ _>_

  *-cancelʳ-≤-pos            : Positive r    → p * r ≤ q * r → p ≤ q
  *-cancelˡ-≤-pos            : Positive r    → r * p ≤ r * q → p ≤ q
  *-cancelʳ-≤-neg            : Negative r    → p * r ≤ q * r → p ≥ q
  *-cancelˡ-≤-neg            : Negative r    → r * p ≤ r * q → p ≥ q
  *-cancelˡ-<-pos            : Positive r    → r * p < r * q → p < q
  *-cancelʳ-<-pos            : Positive r    → p * r < q * r → p < q
  *-cancelˡ-<-neg            : Negative r    → r * p < r * q → p > q
  *-cancelʳ-<-neg            : Negative r    → p * r < q * r → p > q
  *-cancelˡ-<-nonPos         : NonPositive r → r * p < r * q → p > q
  *-cancelʳ-<-nonPos         : NonPositive r → p * r < q * r → p > q
  *-cancelˡ-<-nonNeg         : NonNegative r → r * p < r * q → p < q
  *-cancelʳ-<-nonNeg         : NonNegative r → p * r < q * r → p < q

  neg-distribˡ-*             : - (p * q) ≡ - p * q
  neg-distribʳ-*             : - (p * q) ≡ p * - q

  p≤q⇒p⊔q≡q                  : p ≤ q → p ⊔ q ≡ q
  p≥q⇒p⊔q≡p                  : p ≥ q → p ⊔ q ≡ p
  p≤q⇒p⊓q≡p                  : p ≤ q → p ⊓ q ≡ p
  p≥q⇒p⊓q≡q                  : p ≥ q → p ⊓ q ≡ q

  ⊓-idem                     : Idempotent _⊓_
  ⊓-sel                      : Selective _⊓_
  ⊓-assoc                    : Associative _⊓_
  ⊓-comm                     : Commutative _⊓_

  ⊔-idem                     : Idempotent _⊔_
  ⊔-sel                      : Selective _⊔_
  ⊔-assoc                    : Associative _⊔_
  ⊔-comm                     : Commutative _⊔_

  ⊓-distribˡ-⊔               : _⊓_ DistributesOverˡ _⊔_
  ⊓-distribʳ-⊔               : _⊓_ DistributesOverʳ _⊔_
  ⊓-distrib-⊔                : _⊓_ DistributesOver  _⊔_
  ⊔-distribˡ-⊓               : _⊔_ DistributesOverˡ _⊓_
  ⊔-distribʳ-⊓               : _⊔_ DistributesOverʳ _⊓_
  ⊔-distrib-⊓                : _⊔_ DistributesOver  _⊓_
  ⊓-absorbs-⊔                : _⊓_ Absorbs _⊔_
  ⊔-absorbs-⊓                : _⊔_ Absorbs _⊓_
  ⊔-⊓-absorptive             : Absorptive _⊔_ _⊓_
  ⊓-⊔-absorptive             : Absorptive _⊓_ _⊔_

  ⊓-isMagma                  : IsMagma _⊓_
  ⊓-isSemigroup              : IsSemigroup _⊓_
  ⊓-isCommutativeSemigroup   : IsCommutativeSemigroup _⊓_
  ⊓-isBand                   : IsBand _⊓_
  ⊓-isSemilattice            : IsSemilattice _⊓_
  ⊓-isSelectiveMagma         : IsSelectiveMagma _⊓_

  ⊔-isMagma                  : IsMagma _⊔_
  ⊔-isSemigroup              : IsSemigroup _⊔_
  ⊔-isCommutativeSemigroup   : IsCommutativeSemigroup _⊔_
  ⊔-isBand                   : IsBand _⊔_
  ⊔-isSemilattice            : IsSemilattice _⊔_
  ⊔-isSelectiveMagma         : IsSelectiveMagma _⊔_

  ⊔-⊓-isLattice              : IsLattice _⊔_ _⊓_
  ⊓-⊔-isLattice              : IsLattice _⊓_ _⊔_
  ⊔-⊓-isDistributiveLattice  : IsDistributiveLattice _⊔_ _⊓_
  ⊓-⊔-isDistributiveLattice  : IsDistributiveLattice _⊓_ _⊔_

  ⊓-magma                    : Magma _ _
  ⊓-semigroup                : Semigroup _ _
  ⊓-band                     : Band _ _
  ⊓-commutativeSemigroup     : CommutativeSemigroup _ _
  ⊓-semilattice              : Semilattice _ _
  ⊓-selectiveMagma           : SelectiveMagma _ _

  ⊔-magma                    : Magma _ _
  ⊔-semigroup                : Semigroup _ _
  ⊔-band                     : Band _ _
  ⊔-commutativeSemigroup     : CommutativeSemigroup _ _
  ⊔-semilattice              : Semilattice _ _
  ⊔-selectiveMagma           : SelectiveMagma _ _

  ⊔-⊓-lattice                : Lattice _ _
  ⊓-⊔-lattice                : Lattice _ _
  ⊔-⊓-distributiveLattice    : DistributiveLattice _ _
  ⊓-⊔-distributiveLattice    : DistributiveLattice _ _

  ⊓-glb                      : p ≥ r → q ≥ r → p ⊓ q ≥ r
  ⊓-triangulate              : p ⊓ q ⊓ r ≡ (p ⊓ q) ⊓ (q ⊓ r)
  ⊓-mono-≤                   : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊓-monoˡ-≤                  : (_⊓ p) Preserves _≤_ ⟶ _≤_
  ⊓-monoʳ-≤                  : (p ⊓_) Preserves _≤_ ⟶ _≤_

  ⊔-lub                      : p ≤ r → q ≤ r → p ⊔ q ≤ r
  ⊔-triangulate              : p ⊔ q ⊔ r ≡ (p ⊔ q) ⊔ (q ⊔ r)
  ⊔-mono-≤                   : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊔-monoˡ-≤                  : (_⊔ p) Preserves _≤_ ⟶ _≤_
  ⊔-monoʳ-≤                  : (p ⊔_) Preserves _≤_ ⟶ _≤_

  p⊓q≡q⇒q≤p                  : p ⊓ q ≡ q → q ≤ p
  p⊓q≡p⇒p≤q                  : p ⊓ q ≡ p → p ≤ q
  p⊓q≤p                      : p ⊓ q ≤ p
  p⊓q≤q                      : p ⊓ q ≤ q
  p≤q⇒p⊓r≤q                  : p ≤ q → p ⊓ r ≤ q
  p≤q⇒r⊓p≤q                  : p ≤ q → r ⊓ p ≤ q
  p≤q⊓r⇒p≤q                  : p ≤ q ⊓ r → p ≤ q
  p≤q⊓r⇒p≤r                  : p ≤ q ⊓ r → p ≤ r

  p⊔q≡q⇒p≤q                  : p ⊔ q ≡ q → p ≤ q
  p⊔q≡p⇒q≤p                  : p ⊔ q ≡ p → q ≤ p
  p≤p⊔q                      : p ≤ p ⊔ q
  p≤q⊔p                      : p ≤ q ⊔ p
  p≤q⇒p≤q⊔r                  : p ≤ q → p ≤ q ⊔ r
  p≤q⇒p≤r⊔q                  : p ≤ q → p ≤ r ⊔ q
  p⊔q≤r⇒p≤r                  : p ⊔ q ≤ r → p ≤ r
  p⊔q≤r⇒q≤r                  : p ⊔ q ≤ r → q ≤ r
  p⊓q≤p⊔q                    : p ⊓ q ≤ p ⊔ q

  mono-≤-distrib-⊔           : f Preserves _≤_ ⟶ _≤_ → f (p ⊔ q) ≡ f p ⊔ f q
  mono-≤-distrib-⊓           : f Preserves _≤_ ⟶ _≤_ → f (p ⊓ q) ≡ f p ⊓ f q
  mono-<-distrib-⊓           : f Preserves _<_ ⟶ _<_ → f (p ⊓ q) ≡ f p ⊓ f q
  mono-<-distrib-⊔           : f Preserves _<_ ⟶ _<_ → f (p ⊔ q) ≡ f p ⊔ f q
  antimono-≤-distrib-⊓       : f Preserves _≤_ ⟶ _≥_ → f (p ⊓ q) ≡ f p ⊔ f q
  antimono-≤-distrib-⊔       : f Preserves _≤_ ⟶ _≥_ → f (p ⊔ q) ≡ f p ⊓ f q

  *-distribˡ-⊓-nonNeg        : NonNegative p → p * (q ⊓ r) ≡ (p * q) ⊓ (p * r)
  *-distribʳ-⊓-nonNeg        : NonNegative p → (q ⊓ r) * p ≡ (q * p) ⊓ (r * p)
  *-distribˡ-⊔-nonNeg        : NonNegative p → p * (q ⊔ r) ≡ (p * q) ⊔ (p * r)
  *-distribʳ-⊔-nonNeg        : NonNegative p → (q ⊔ r) * p ≡ (q * p) ⊔ (r * p)
  *-distribˡ-⊔-nonPos        : NonPositive p → p * (q ⊔ r) ≡ (p * q) ⊓ (p * r)
  *-distribʳ-⊔-nonPos        : NonPositive p → (q ⊔ r) * p ≡ (q * p) ⊓ (r * p)
  *-distribˡ-⊓-nonPos        : NonPositive p → p * (q ⊓ r) ≡ (p * q) ⊔ (p * r)
  *-distribʳ-⊓-nonPos        : NonPositive p → (q ⊓ r) * p ≡ (q * p) ⊔ (r * p)

  1/-involutive              : 1/ (1/ p) ≡ p
  pos⇒1/pos                  : Positive p → Positive (1/ p)
  neg⇒1/neg                  : Negative p → Negative (1/ p)
  1/pos⇒pos                  : Positive (1/ p) → Positive p
  1/neg⇒neg                  : Negative (1/ p) → Negative p

  toℚᵘ-homo-∣_∣              : Homomorphic₁ toℚᵘ ∣_∣ ℚᵘ.∣_∣
  ∣-∣-nonNeg                 : NonNegative ∣ p ∣
  0≤∣p∣                      : 0ℚ ≤ ∣ p ∣
  0≤p⇒∣p∣≡p                  : 0ℚ ≤ p → ∣ p ∣ ≡ p
  ∣-p∣≡∣p∣                   : ∣ - p ∣ ≡ ∣ p ∣
  ∣p∣≡p⇒p≡0                  : ∣ p ∣ ≡ 0ℚ → p ≡ 0ℚ
  ∣p∣≡p⊎∣p∣≡-p               : ∣ p ∣ ≡ p ⊎ ∣ p ∣ ≡ - p
  ∣p+q∣≤∣p∣+∣q∣              : ∣ p + q ∣ ≤ ∣ p ∣ + ∣ q ∣
  ∣p-q∣≤∣p∣+∣q∣              : ∣ p - q ∣ ≤ ∣ p ∣ + ∣ q ∣
  ∣p*q∣≡∣p∣*∣q∣              : ∣ p * q ∣ ≡ ∣ p ∣ * ∣ q ∣
  ```

* Add new relations and functions to `Data.Rational.Unnormalised`:
  ```agda
  _≤ᵇ_ : ℤ → ℤ → Bool
  _⊔_  : (p q : ℚᵘ) → ℚᵘ
  _⊓_  : (p q : ℚᵘ) → ℚᵘ
  ∣_∣  : ℚᵘ → ℚᵘ
  ```

* Add new proofs to `Data.Rational.Unnormalised.Properties`:
  ```agda
  /-cong                    : p₁ ≡ p₂ → q₁ ≡ q₂ → p₁ / q₁ ≡ p₂ / q₂
  ↥[p/q]≡p                  : ↥ (p / q) ≡ p
  ↧[p/q]≡q                  : ↧ (p / q) ≡ ℤ.+ q

  ≤-respˡ-≃                 : _≤_ Respectsˡ _≃_
  ≤-respʳ-≃                 : _≤_ Respectsʳ _≃_
  ≤-resp₂-≃                 : _≤_ Respects₂ _≃_

  ≤-isPreorder              : IsPreorder _≃_ _≤_
  ≤-isPreorder-≡            : IsPreorder _≡_ _≤_
  ≤-isTotalPreorder         : IsTotalPreorder _≃_ _≤_
  ≤-isTotalPreorder-≡       : IsTotalPreorder _≡_ _≤_
  ≤-preorder                : Preorder 0ℓ 0ℓ 0ℓ
  ≤-preorder-≡              : Preorder 0ℓ 0ℓ 0ℓ
  ≤-totalPreorder           : TotalPreorder 0ℓ 0ℓ 0ℓ
  ≤-totalPreorder-≡         : TotalPreorder 0ℓ 0ℓ 0ℓ

  ≤ᵇ⇒≤                      : T (p ≤ᵇ q) → p ≤ q
  ≤⇒≤ᵇ                      : p ≤ q → T (p ≤ᵇ q)

  neg-cancel-<              : - p < - q → q < p
  neg-cancel-≤-≥            : - p ≤ - q → q ≤ p

  mono⇒cong                 : f Preserves _≤_ ⟶ _≤_ → f Preserves _≃_ ⟶ _≃_
  antimono⇒cong             : f Preserves _≤_ ⟶ _≥_ → f Preserves _≃_ ⟶ _≃_

  *-congˡ                   : LeftCongruent _≃_ _*_
  *-congʳ                   : RightCongruent _≃_ _*_

  *-cancelˡ-/               : (ℤ.+ p ℤ.* q) / (p ℕ.* r) ≃ q / r
  *-cancelʳ-/               : (q ℤ.* ℤ.+ p) / (r ℕ.* p) ≃ q / r

  *-cancelʳ-≤-neg           : Negative r → p * r ≤ q * r → q ≤ p
  *-cancelˡ-≤-neg           : Negative r → r * p ≤ r * q → q ≤ p
  *-monoˡ-≤-nonPos          : NonPositive r → (_* r) Preserves _≤_ ⟶ _≥_
  *-monoʳ-≤-nonPos          : NonPositive r → (r *_) Preserves _≤_ ⟶ _≥_
  *-monoˡ-≤-neg             : Negative r → (_* r) Preserves _≤_ ⟶ _≥_
  *-monoʳ-≤-neg             : Negative r → (r *_) Preserves _≤_ ⟶ _≥_

  *-cancelˡ-<-pos           : Positive r → r * p < r * q → p < q
  *-cancelʳ-<-pos           : Positive r → p * r < q * r → p < q
  *-monoˡ-<-neg             : Negative r → (_* r) Preserves _<_ ⟶ _>_
  *-monoʳ-<-neg             : Negative r → (r *_) Preserves _<_ ⟶ _>_
  *-cancelˡ-<-nonPos        : NonPositive r → r * p < r * q → q < p
  *-cancelʳ-<-nonPos        : NonPositive r → p * r < q * r → q < p
  *-cancelˡ-<-neg           : Negative r → r * p < r * q → q < p
  *-cancelʳ-<-neg           : Negative r → p * r < q * r → q < p

  pos⇒1/pos                 : Positive q → Positive (1/ q)
  neg⇒1/neg                 : Negative q → Negative (1/ q)
  1/-involutive-≡           : 1/ (1/ q) ≡ q
  1/-involutive             : 1/ (1/ q) ≃ q
  p>1⇒1/p<1                 : p > 1ℚᵘ → (1/ p) < 1ℚᵘ

  ⊓-congˡ                   : LeftCongruent _≃_ _⊓_
  ⊓-congʳ                   : RightCongruent _≃_ _⊓_
  ⊓-cong                    : Congruent₂ _≃_ _⊓_
  ⊓-idem                    : Idempotent _≃_ _⊓_
  ⊓-sel                     : Selective _≃_ _⊓_
  ⊓-assoc                   : Associative _≃_ _⊓_
  ⊓-comm                    : Commutative _≃_ _⊓_

  ⊔-congˡ                   : LeftCongruent _≃_ _⊔_
  ⊔-congʳ                   : RightCongruent _≃_ _⊔_
  ⊔-cong                    : Congruent₂ _≃_ _⊔_
  ⊔-idem                    : Idempotent _≃_ _⊔_
  ⊔-sel                     : Selective _≃_ _⊔_
  ⊔-assoc                   : Associative _≃_ _⊔_
  ⊔-comm                    : Commutative _≃_ _⊔_

  ⊓-distribˡ-⊔              : _DistributesOverˡ_ _≃_ _⊓_ _⊔_
  ⊓-distribʳ-⊔              : _DistributesOverʳ_ _≃_ _⊓_ _⊔_
  ⊓-distrib-⊔               : _DistributesOver_  _≃_ _⊓_ _⊔_
  ⊔-distribˡ-⊓              : _DistributesOverˡ_ _≃_ _⊔_ _⊓_
  ⊔-distribʳ-⊓              : _DistributesOverʳ_ _≃_ _⊔_ _⊓_
  ⊔-distrib-⊓               : _DistributesOver_  _≃_ _⊔_ _⊓_
  ⊓-absorbs-⊔               : _Absorbs_ _≃_ _⊓_ _⊔_
  ⊔-absorbs-⊓               : _Absorbs_ _≃_ _⊔_ _⊓_
  ⊔-⊓-absorptive            : Absorptive _≃_ _⊔_ _⊓_
  ⊓-⊔-absorptive            : Absorptive _≃_ _⊓_ _⊔_

  ⊓-isMagma                 : IsMagma _≃_ _⊓_
  ⊓-isSemigroup             : IsSemigroup _≃_ _⊓_
  ⊓-isCommutativeSemigroup  : IsCommutativeSemigroup _≃_ _⊓_
  ⊓-isBand                  : IsBand _≃_ _⊓_
  ⊓-isSemilattice           : IsSemilattice _≃_ _⊓_
  ⊓-isSelectiveMagma        : IsSelectiveMagma _≃_ _⊓_

  ⊔-isMagma                 : IsMagma _≃_ _⊔_
  ⊔-isSemigroup             : IsSemigroup _≃_ _⊔_
  ⊔-isCommutativeSemigroup  : IsCommutativeSemigroup _≃_ _⊔_
  ⊔-isBand                  : IsBand _≃_ _⊔_
  ⊔-isSemilattice           : IsSemilattice _≃_ _⊔_
  ⊔-isSelectiveMagma        : IsSelectiveMagma _≃_ _⊔_

  ⊔-⊓-isLattice             : IsLattice _≃_ _⊔_ _⊓_
  ⊓-⊔-isLattice             : IsLattice _≃_ _⊓_ _⊔_
  ⊔-⊓-isDistributiveLattice : IsDistributiveLattice _≃_ _⊔_ _⊓_
  ⊓-⊔-isDistributiveLattice : IsDistributiveLattice _≃_ _⊓_ _⊔_

  ⊓-rawMagma                : RawMagma _ _
  ⊔-rawMagma                : RawMagma _ _
  ⊔-⊓-rawLattice            : RawLattice _ _

  ⊓-magma                   : Magma _ _
  ⊓-semigroup               : Semigroup _ _
  ⊓-band                    : Band _ _
  ⊓-commutativeSemigroup    : CommutativeSemigroup _ _
  ⊓-semilattice             : Semilattice _ _
  ⊓-selectiveMagma          : SelectiveMagma _ _

  ⊔-magma                   : Magma _ _
  ⊔-semigroup               : Semigroup _ _
  ⊔-band                    : Band _ _
  ⊔-commutativeSemigroup    : CommutativeSemigroup _ _
  ⊔-semilattice             : Semilattice _ _
  ⊔-selectiveMagma          : SelectiveMagma _ _

  ⊔-⊓-lattice               : Lattice _ _
  ⊓-⊔-lattice               : Lattice _ _
  ⊔-⊓-distributiveLattice   : DistributiveLattice _ _
  ⊓-⊔-distributiveLattice   : DistributiveLattice _ _

  ⊓-triangulate             : p ⊓ q ⊓ r ≃ (p ⊓ q) ⊓ (q ⊓ r)
  ⊔-triangulate             : p ⊔ q ⊔ r ≃ (p ⊔ q) ⊔ (q ⊔ r)

  ⊓-glb                     : p ≥ r → q ≥ r → p ⊓ q ≥ r
  ⊓-mono-≤                  : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊓-monoˡ-≤                 : (_⊓ p) Preserves _≤_ ⟶ _≤_
  ⊓-monoʳ-≤                 : (p ⊓_) Preserves _≤_ ⟶ _≤_

  ⊔-lub                     : p ≤ r → q ≤ r → p ⊔ q ≤ r
  ⊔-mono-≤                  : _⊔_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊔-monoˡ-≤                 : (_⊔ p) Preserves _≤_ ⟶ _≤_
  ⊔-monoʳ-≤                 : (p ⊔_) Preserves _≤_ ⟶ _≤_

  p⊓q≃q⇒q≤p                 : p ⊓ q ≃ q → q ≤ p
  p⊓q≃p⇒p≤q                 : p ⊓ q ≃ p → p ≤ q
  p⊔q≃q⇒p≤q                 : p ⊔ q ≃ q → p ≤ q
  p⊔q≃p⇒q≤p                 : p ⊔ q ≃ p → q ≤ p

  p⊓q≤p                     : p ⊓ q ≤ p
  p⊓q≤q                     : p ⊓ q ≤ q
  p≤q⇒p⊓r≤q                 : p ≤ q → p ⊓ r ≤ q
  p≤q⇒r⊓p≤q                 : p ≤ q → r ⊓ p ≤ q
  p≤q⊓r⇒p≤q                 : p ≤ q ⊓ r → p ≤ q
  p≤q⊓r⇒p≤r                 : p ≤ q ⊓ r → p ≤ r

  p≤p⊔q                     : p ≤ p ⊔ q
  p≤q⊔p                     : p ≤ q ⊔ p
  p≤q⇒p≤q⊔r                 : p ≤ q → p ≤ q ⊔ r
  p≤q⇒p≤r⊔q                 : p ≤ q → p ≤ r ⊔ q
  p⊔q≤r⇒p≤r                 : p ⊔ q ≤ r → p ≤ r
  p⊔q≤r⇒q≤r                 : p ⊔ q ≤ r → q ≤ r

  p≤q⇒p⊔q≃q                 : p ≤ q → p ⊔ q ≃ q
  p≥q⇒p⊔q≃p                 : p ≥ q → p ⊔ q ≃ p
  p≤q⇒p⊓q≃p                 : p ≤ q → p ⊓ q ≃ p
  p≥q⇒p⊓q≃q                 : p ≥ q → p ⊓ q ≃ q
  p⊓q≤p⊔q                   : p ⊓ q ≤ p ⊔ q

  mono-≤-distrib-⊔          : f Preserves _≤_ ⟶ _≤_ → f (m ⊔ n) ≃ f m ⊔ f n
  mono-≤-distrib-⊓          : f Preserves _≤_ ⟶ _≤_ → f (m ⊓ n) ≃ f m ⊓ f n
  antimono-≤-distrib-⊓      : f Preserves _≤_ ⟶ _≥_ → f (m ⊓ n) ≃ f m ⊔ f n
  antimono-≤-distrib-⊔      : f Preserves _≤_ ⟶ _≥_ → f (m ⊔ n) ≃ f m ⊓ f n

  neg-distrib-⊔-⊓           : - (p ⊔ q) ≃ - p ⊓ - q
  neg-distrib-⊓-⊔           : - (p ⊓ q) ≃ - p ⊔ - q

  *-distribˡ-⊓-nonNeg       : NonNegative p → p * (q ⊓ r) ≃ (p * q) ⊓ (p * r)
  *-distribʳ-⊓-nonNeg       : NonNegative p → (q ⊓ r) * p ≃ (q * p) ⊓ (r * p)
  *-distribˡ-⊔-nonNeg       : NonNegative p → p * (q ⊔ r) ≃ (p * q) ⊔ (p * r)
  *-distribʳ-⊔-nonNeg       : NonNegative p → (q ⊔ r) * p ≃ (q * p) ⊔ (r * p)
  *-distribˡ-⊔-nonPos       : NonPositive p → p * (q ⊔ r) ≃ (p * q) ⊓ (p * r)
  *-distribʳ-⊔-nonPos       : NonPositive p → (q ⊔ r) * p ≃ (q * p) ⊓ (r * p)
  *-distribˡ-⊓-nonPos       : NonPositive p → p * (q ⊓ r) ≃ (p * q) ⊔ (p * r)
  *-distribʳ-⊓-nonPos       : NonPositive p → (q ⊓ r) * p ≃ (q * p) ⊔ (r * p)

  ∣-∣-cong                  : p ≃ q → ∣ p ∣ ≃ ∣ q ∣
  ∣p∣≃0⇒p≃0                 : ∣ p ∣ ≃ 0ℚᵘ → p ≃ 0ℚᵘ
  ∣-p∣≡∣p∣                  : ∣ - p ∣ ≡ ∣ p ∣
  ∣-p∣≃∣p∣                  : ∣ - p ∣ ≃ ∣ p ∣
  0≤p⇒∣p∣≡p                 : 0ℚᵘ ≤ p → ∣ p ∣ ≡ p
  0≤p⇒∣p∣≃p                 : 0ℚᵘ ≤ p → ∣ p ∣ ≃ p
  ∣p∣≡p⇒0≤p                 : ∣ p ∣ ≡ p → 0ℚᵘ ≤ p
  ∣p∣≡p∨∣p∣≡-p              : (∣ p ∣ ≡ p) ⊎ (∣ p ∣ ≡ - p)
  ∣p+q∣≤∣p∣+∣q∣             : ∣ p + q ∣ ≤ ∣ p ∣ + ∣ q ∣
  ∣p-q∣≤∣p∣+∣q∣             : ∣ p - q ∣ ≤ ∣ p ∣ + ∣ q ∣
  ∣p*q∣≡∣p∣*∣q∣             : ∣ p * q ∣ ≡ ∣ p ∣ * ∣ q ∣
  ∣p*q∣≃∣p∣*∣q∣             : ∣ p * q ∣ ≃ ∣ p ∣ * ∣ q ∣
  ```

* Added new function to `Data.Tree.Rose`:
  ```agda
  fromBinary : (A → C) → (B → C) → Tree.Binary A B → Rose C ∞
  ```

* Added new definitions to `IO`:
  ```agda
  getLine : IO String
  Main : Set
  ```

* Added new functions to `Codata.Stream`:
  ```agda
  nats : Stream ℕ ∞

  interleave⁺ : List⁺ (Stream A i) → Stream A i
  cantor      : Stream (Stream A ∞) ∞ → Stream A ∞
  plane       : Stream A ∞ → ((a : A) → Stream (B a) ∞) → Stream (Σ A B) ∞
  ```

  * Added new definitions to `Relation.Binary.Bundles`:
  ```agda
  record TotalPreorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂))
  ```

* Added new definitions to `Relation.Binary.Structures`:
  ```agda
  record IsTotalPreorder (_≲_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂)
  ```

* Added new proofs to `Relation.Binary.Properties.Poset`:
  ```agda
  mono⇒cong     : f Preserves _≤_ ⟶ _≤_ → f Preserves _≈_ ⟶ _≈_
  antimono⇒cong : f Preserves _≤_ ⟶ _≥_ → f Preserves _≈_ ⟶ _≈_
  ```

* Added new proofs to `Relation.Binary.Consequences`:
  ```agda
  mono⇒cong     : Symmetric ≈₁ → ≈₁ ⇒ ≤₁ → Antisymmetric ≈₂ ≤₂ → ∀ {f} → f Preserves ≤₁ ⟶ ≤₂        → f Preserves ≈₁ ⟶ ≈₂
  antimono⇒cong : Symmetric ≈₁ → ≈₁ ⇒ ≤₁ → Antisymmetric ≈₂ ≤₂ → ∀ {f} → f Preserves ≤₁ ⟶ (flip ≤₂) → f Preserves ≈₁ ⟶ ≈₂
  ```

* Added new proofs to `Relation.Binary.Construct.Converse`:
  ```agda
  totalPreorder   : TotalPreorder a ℓ₁ ℓ₂ → TotalPreorder a ℓ₁ ℓ₂
  isTotalPreorder : IsTotalPreorder ≈ ∼  → IsTotalPreorder ≈ (flip ∼)
  ```


* Added new proofs to `Relation.Binary.Morphism.Construct.Constant`:
  ```agda
  setoidHomomorphism : (S : Setoid a ℓ₁) (T : Setoid b ℓ₂) → ∀ x → SetoidHomomorphism S T
  preorderHomomorphism : (P : Preorder a ℓ₁ ℓ₂) (Q : Preorder b ℓ₃ ℓ₄) → ∀ x → PreorderHomomorphism P Q
  ```

* Added new proofs to `Relation.Binary.Morphism.Construct.Composition`:
  ```agda
  setoidHomomorphism : SetoidHomomorphism S T → SetoidHomomorphism T U → SetoidHomomorphism S U
  setoidMonomorphism : SetoidMonomorphism S T → SetoidMonomorphism T U → SetoidMonomorphism S U
  setoidIsomorphism  : SetoidIsomorphism S T → SetoidIsomorphism T U → SetoidIsomorphism S U
  
  preorderHomomorphism : PreorderHomomorphism P Q → PreorderHomomorphism Q R → PreorderHomomorphism P R
  posetHomomorphism    : PosetHomomorphism P Q → PosetHomomorphism Q R → PosetHomomorphism P R
  ```

* Added new proofs to `Relation.Binary.Morphism.Construct.Identity`:
  ```agda
  setoidHomomorphism : (S : Setoid a ℓ₁) → SetoidHomomorphism S S
  setoidMonomorphism : (S : Setoid a ℓ₁) → SetoidMonomorphism S S
  setoidIsomorphism  : (S : Setoid a ℓ₁) → SetoidIsomorphism S S
  
  preorderHomomorphism : (P : Preorder a ℓ₁ ℓ₂) → PreorderHomomorphism P P
  posetHomomorphism    : (P : Poset a ℓ₁ ℓ₂) → PosetHomomorphism P P
  ```

* Added new proofs to `Relation.Nullary.Negation`:
  ```agda
  contradiction₂ : P ⊎ Q → ¬ P → ¬ Q → Whatever
  ```
