Version 2.1-dev
===============

The library has been tested using Agda 2.6.4, 2.6.4.1, and 2.6.4.3.

Highlights
----------

Bug-fixes
---------

* Fix statement of `Data.Vec.Properties.toList-replicate`, where `replicate`
  was mistakenly applied to the level of the type `A` instead of the
  variable `x` of type `A`.

* Module `Data.List.Relation.Ternary.Appending.Setoid.Properties` no longer
  exports the `Setoid` module under the alias `S`.

Non-backwards compatible changes
--------------------------------

* The modules and morphisms in `Algebra.Module.Morphism.Structures` are now
  parametrized by _raw_ bundles rather than lawful bundles, in line with other
  modules defining morphism structures.
* The definitions in `Algebra.Module.Morphism.Construct.Composition` are now
  parametrized by _raw_ bundles, and as such take a proof of transitivity.
* The definitions in `Algebra.Module.Morphism.Construct.Identity` are now
  parametrized by _raw_ bundles, and as such take a proof of reflexivity.

Other major improvements
------------------------

Deprecated modules
------------------

* `Data.List.Relation.Binary.Sublist.Propositional.Disjoint` deprecated in favour of
  `Data.List.Relation.Binary.Sublist.Propositional.Slice`.

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

* In `Data.Nat.Divisibility.Core`:
  ```agda
  *-pres-∣  ↦  Data.Nat.Divisibility.*-pres-∣
  ```

New modules
-----------

* Bundles for left- and right- actions:
  ```
  Algebra.Action.Bundles
  ```

* The free `List` actions over a `SetoidAction`:
  ```
  Algebra.Action.Construct.Free
  ```

* The left- and right- regular actions (of a `Monoid`) over itself:
  ```
  Algebra.Action.Construct.Self
  ```

* Raw structures for left- and right- actions:
  ```
  Algebra.Action.Structures.Raw
  ```

* Raw bundles for module-like algebraic structures:
  ```
  Algebra.Module.Bundles.Raw
  ```

* Prime factorisation of natural numbers.
  ```
  Data.Nat.Primality.Factorisation
  ```

* Consequences of 'infinite descent' for (accessible elements of) well-founded relations:
  ```agda
  Induction.InfiniteDescent
  ```

* The unique morphism from the initial, resp. terminal, algebra:
  ```agda
  Algebra.Morphism.Construct.Initial
  Algebra.Morphism.Construct.Terminal
  ```

* Nagata's construction of the "idealization of a module":
  ```agda
  Algebra.Module.Construct.Idealization
  ```

* `Data.List.Relation.Binary.Sublist.Propositional.Slice`
  replacing `Data.List.Relation.Binary.Sublist.Propositional.Disjoint` (*)
  and adding new functions:
  - `⊆-upper-bound-is-cospan` generalising `⊆-disjoint-union-is-cospan` from (*)
  - `⊆-upper-bound-cospan` generalising `⊆-disjoint-union-cospan` from (*)

* `Data.Vec.Functional.Relation.Binary.Permutation`, defining:
  ```agda
  _↭_ : IRel (Vector A) _
  ```

* `Data.Vec.Functional.Relation.Binary.Permutation.Properties` of the above:
  ```agda
  ↭-refl      : Reflexive (Vector A) _↭_
  ↭-reflexive : xs ≡ ys → xs ↭ ys
  ↭-sym       : Symmetric (Vector A) _↭_
  ↭-trans     : Transitive (Vector A) _↭_
  isIndexedEquivalence : {A : Set a} → IsIndexedEquivalence (Vector A) _↭_
  indexedSetoid        : {A : Set a} → IndexedSetoid ℕ a _
  ```

* `Function.Relation.Binary.Equality`
  ```agda
  setoid : Setoid a₁ a₂ → Setoid b₁ b₂ → Setoid _ _
  ```
  and a convenient infix version
  ```agda
  _⇨_ = setoid
  ```

* Symmetric interior of a binary relation
  ```
  Relation.Binary.Construct.Interior.Symmetric
  ```

* Pointwise and equality relations over indexed containers:
  ```agda
  Data.Container.Indexed.Relation.Binary.Pointwise
  Data.Container.Indexed.Relation.Binary.Pointwise.Properties
  Data.Container.Indexed.Relation.Binary.Equality.Setoid
  ```

Additions to existing modules
-----------------------------

* Exporting more `Raw` substructures from `Algebra.Bundles.Ring`:
  ```agda
  rawNearSemiring   : RawNearSemiring _ _
  rawRingWithoutOne : RawRingWithoutOne _ _
  +-rawGroup        : RawGroup _ _
  ```

* In `Algebra.Module.Bundles`, raw bundles are re-exported and the bundles expose their raw counterparts.

* In `Algebra.Module.Construct.DirectProduct`:
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

* In `Algebra.Module.Construct.TensorUnit`:
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

* In `Algebra.Module.Construct.Zero`:
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

* In `Algebra.Properties.Group`:
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
  \\≗flip-//⇒comm : (∀ x y → x \\ y ≈ y // x) → Commutative _∙_
  comm⇒\\≗flip-// : Commutative _∙_ → ∀ x y → x \\ y ≈ y // x
  ```

* In `Algebra.Properties.Loop`:
  ```agda
  identityˡ-unique : x ∙ y ≈ y → x ≈ ε
  identityʳ-unique : x ∙ y ≈ x → y ≈ ε
  identity-unique  : Identity x _∙_ → x ≈ ε
  ```

* In `Algebra.Construct.Terminal`:
  ```agda
  rawNearSemiring : RawNearSemiring c ℓ
  nearSemiring    : NearSemiring c ℓ
  ```

* In `Algebra.Properties.Monoid.Mult`:
  ```agda
  ×-homo-0 : ∀ x → 0 × x ≈ 0#
  ×-homo-1 : ∀ x → 1 × x ≈ x
  ```

* In `Algebra.Properties.Semiring.Mult`:
  ```agda
  ×-homo-0#     : ∀ x → 0 × x ≈ 0# * x
  ×-homo-1#     : ∀ x → 1 × x ≈ 1# * x
  idem-×-homo-* : (_*_ IdempotentOn x) → (m × x) * (n × x) ≈ (m ℕ.* n) × x
  ```

* In `Algebra.Structures.IsGroup`:
  ```agda
  infixl 6 _//_
  _//_ : Op₂ A
  x // y = x ∙ (y ⁻¹)
  infixr 6 _\\_
  _\\_ : Op₂ A
  x \\ y = (x ⁻¹) ∙ y
  ```

* In `Data.Container.Indexed.Core`:
  ```agda
  Subtrees o c = (r : Response c) → X (next c r)
  ```

* In `Data.Fin.Properties`:
  ```agda
  nonZeroIndex : Fin n → ℕ.NonZero n
  ```

* In `Data.Integer.Divisibility`: introduce `divides` as an explicit pattern synonym
  ```agda
  pattern divides k eq = Data.Nat.Divisibility.divides k eq
  ```

* In `Data.Integer.Properties`:
  ```agda
  ◃-nonZero : .{{_ : ℕ.NonZero n}} → NonZero (s ◃ n)
  sign-*    : .{{NonZero (i * j)}} → sign (i * j) ≡ sign i Sign.* sign j
  i*j≢0     : .{{_ : NonZero i}} .{{_ : NonZero j}} → NonZero (i * j)
  ```

* In `Data.List.Properties`:
  ```agda
  applyUpTo-∷ʳ          : applyUpTo f n ∷ʳ f n ≡ applyUpTo f (suc n)
  applyDownFrom-∷ʳ      : applyDownFrom (f ∘ suc) n ∷ʳ f 0 ≡ applyDownFrom f (suc n)
  upTo-∷ʳ               : upTo n ∷ʳ n ≡ upTo (suc n)
  downFrom-∷ʳ           : applyDownFrom suc n ∷ʳ 0 ≡ downFrom (suc n)
  reverse-applyUpTo     : reverse (applyUpTo f n) ≡ applyDownFrom f n
  reverse-upTo          : reverse (upTo n) ≡ downFrom n
  reverse-applyDownFrom : reverse (applyDownFrom f n) ≡ applyUpTo f n
  reverse-downFrom      : reverse (downFrom n) ≡ upTo n
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

* In `Data.List.Relation.Binary.Pointwise.Base`:
  ```agda
  unzip : Pointwise (R ; S) ⇒ (Pointwise R ; Pointwise S)
  ```

* In `Data.Maybe.Relation.Binary.Pointwise`:
  ```agda
  pointwise⊆any : Pointwise R (just x) ⊆ Any (R x)
  ```

* In `Data.List.Relation.Binary.Sublist.Setoid`:
  ```agda
  ⊆-upper-bound : ∀ {xs ys zs} (τ : xs ⊆ zs) (σ : ys ⊆ zs) → UpperBound τ σ
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

* Added new proofs in `Data.Nat.Properties`:
  ```agda
  m≤n+o⇒m∸n≤o : ∀ m n {o} → m ≤ n + o → m ∸ n ≤ o
  m<n+o⇒m∸n<o : ∀ m n {o} → .{{NonZero o}} → m < n + o → m ∸ n < o
  pred-cancel-≤ : pred m ≤ pred n → (m ≡ 1 × n ≡ 0) ⊎ m ≤ n
  pred-cancel-< : pred m < pred n → m < n
  pred-injective : .{{NonZero m}} → .{{NonZero n}} → pred m ≡ pred n → m ≡ n
  pred-cancel-≡ : pred m ≡ pred n → ((m ≡ 0 × n ≡ 1) ⊎ (m ≡ 1 × n ≡ 0)) ⊎ m ≡ n
  ```

* Added new proofs to `Data.Nat.Primality`:
  ```agda
  rough∧square>⇒prime : .{{NonTrivial n}} → m Rough n → m * m > n → Prime n
  productOfPrimes≢0 : All Prime as → NonZero (product as)
  productOfPrimes≥1 : All Prime as → product as ≥ 1
  ```

* Added new proofs to `Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  product-↭ : product Preserves _↭_ ⟶ _≡_
  ```

* Added new functions in `Data.String.Base`:
  ```agda
  map : (Char → Char) → String → String

* Added new definition in `Relation.Binary.Construct.Closure.Transitive`
  ```
  transitive⁻ : Transitive _∼_ → TransClosure _∼_ ⇒ _∼_
  ```

* Added new definition in `Relation.Unary`
  ```
  Stable : Pred A ℓ → Set _
  ```

* In `Function.Bundles`, added `_⟶ₛ_` as a synonym for `Func` that can
  be used infix.

* Added new proofs in `Relation.Binary.Construct.Composition`:
  ```agda
  transitive⇒≈;≈⊆≈ : Transitive ≈ → (≈ ; ≈) ⇒ ≈
  ```

* Added new definitions in `Relation.Binary.Definitions`
  ```
  Stable _∼_ = ∀ x y → Nullary.Stable (x ∼ y)
  Empty  _∼_ = ∀ {x y} → x ∼ y → ⊥
  ```

* Added new proofs in `Relation.Binary.Properties.Setoid`:
  ```agda
  ≈;≈⇒≈ : _≈_ ; _≈_ ⇒ _≈_
  ≈⇒≈;≈ : _≈_ ⇒ _≈_ ; _≈_
  ```

* Added new definitions in `Relation.Nullary`
  ```
  Recomputable    : Set _
  WeaklyDecidable : Set _
  ```

* Added new proof in `Relation.Nullary.Decidable`:
  ```agda
  ⌊⌋-map′ : (a? : Dec A) → ⌊ map′ t f a? ⌋ ≡ ⌊ a? ⌋
  ```

* Added new definitions in `Relation.Unary`
  ```
  Stable          : Pred A ℓ → Set _
  WeaklyDecidable : Pred A ℓ → Set _
  ```

* `Tactic.Cong` now provides a marker function, `⌞_⌟`, for user-guided
  anti-unification. See README.Tactic.Cong for details.
