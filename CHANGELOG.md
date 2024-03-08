Version 2.1-dev
===============

The library has been tested using Agda 2.6.4 and 2.6.4.1.

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

Deprecated names
----------------

* In `Algebra.Properties.Semiring.Mult`:
  ```agda
  1×-identityʳ  ↦  ×-homo-1
  ```

* In `Data.Nat.Divisibility.Core`:
  ```agda
  *-pres-∣  ↦  Data.Nat.Divisibility.*-pres-∣
  ```

New modules
-----------
* `Algebra.Module.Bundles.Raw`: raw bundles for module-like algebraic structures

* Nagata's construction of the "idealization of a module":
  ```agda
  Algebra.Module.Construct.Idealization
  ```

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

* In `Data.Fin.Properties`:
  ```agda
  nonZeroIndex : Fin n → ℕ.NonZero n
  ```

* In `Data.Integer.Divisisbility`: introduce `divides` as an explicit pattern synonym
  ```agda
  pattern divides k eq = Data.Nat.Divisibility.divides k eq
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

* Added new functions in `Data.String.Base`:
  ```agda
  map : (Char → Char) → String → String
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
