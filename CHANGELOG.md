Version 2.2-dev
===============

The library has been tested using Agda 2.7.0.

Highlights
----------

Bug-fixes
---------

* Removed unnecessary parameter `#-trans : Transitive _#_` from
  `Relation.Binary.Reasoning.Base.Apartness`.

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Properties.CommutativeMagma.Divisibility`:
  ```agda
  ∣-factors    ↦  x|xy∧y|xy
  ∣-factors-≈  ↦  xy≈z⇒x|z∧y|z
  ```

* In `Algebra.Properties.Magma.Divisibility`:
  ```agda
  ∣-respˡ   ↦  ∣-respˡ-≈
  ∣-respʳ   ↦  ∣-respʳ-≈
  ∣-resp    ↦  ∣-resp-≈
 ```

* In `Algebra.Solver.CommutativeMonoid`:
  ```agda
  normalise-correct  ↦  Algebra.Solver.CommutativeMonoid.Normal.correct
  sg                 ↦  Algebra.Solver.CommutativeMonoid.Normal.singleton
  sg-correct         ↦  Algebra.Solver.CommutativeMonoid.Normal.singleton-correct
  ```

* In `Algebra.Solver.IdempotentCommutativeMonoid`:
  ```agda
  flip12             ↦  Algebra.Properties.CommutativeSemigroup.xy∙z≈y∙xz
  distr              ↦  Algebra.Properties.IdempotentCommutativeMonoid.∙-distrˡ-∙
  normalise-correct  ↦  Algebra.Solver.IdempotentCommutativeMonoid.Normal.correct
  sg                 ↦  Algebra.Solver.IdempotentCommutativeMonoid.Normal.singleton
  sg-correct         ↦  Algebra.Solver.IdempotentCommutativeMonoid.Normal.singleton-correct
  ```

* In `Algebra.Solver.Monoid`:
  ```agda
  homomorphic        ↦  Algebra.Solver.Monoid.Normal.comp-correct
  normalise-correct  ↦  Algebra.Solver.Monoid.Normal.correct
  ```

* In `Data.Vec.Properties`:
  ```agda
  ++-assoc _      ↦  ++-assoc-eqFree
  ++-identityʳ _  ↦  ++-identityʳ-eqFree
  unfold-∷ʳ _     ↦  unfold-∷ʳ-eqFree
  ++-∷ʳ _         ↦  ++-∷ʳ-eqFree
  ∷ʳ-++ _         ↦  ∷ʳ-++-eqFree
  reverse-++ _    ↦  reverse-++-eqFree
  ∷-ʳ++ _         ↦  ∷-ʳ++-eqFree
  ++-ʳ++ _        ↦  ++-ʳ++-eqFree
  ʳ++-ʳ++ _       ↦  ʳ++-ʳ++-eqFree
  ```

New modules
-----------

* Properties of `IdempotentCommutativeMonoid`s refactored out from `Algebra.Solver.IdempotentCommutativeMonoid`:
  ```agda
  Algebra.Properties.IdempotentCommutativeMonoid
  ```

* Refactoring of the `Algebra.Solver.*Monoid` implementations, via
  a single `Solver` module API based on the existing `Expr`, and
  a common `Normal`-form API:
  ```agda
  Algebra.Solver.CommutativeMonoid.Normal
  Algebra.Solver.IdempotentCommutativeMonoid.Normal
  Algebra.Solver.Monoid.Expression
  Algebra.Solver.Monoid.Normal
  Algebra.Solver.Monoid.Solver
  ```

  NB Imports of the existing proof procedures `solve` and `prove` etc. should still be via the top-level interfaces in `Algebra.Solver.*Monoid`.

* Refactored out from `Data.List.Relation.Unary.All.Properties` in order to break a dependency cycle with `Data.List.Membership.Setoid.Properties`:
  ```agda
  Data.List.Relation.Unary.All.Properties.Core
  ```

* `Data.List.Relation.Binary.Disjoint.Propositional.Properties`:
  Propositional counterpart to `Data.List.Relation.Binary.Disjoint.Setoid.Properties`

* `Data.List.Relation.Binary.Permutation.Propositional.Properties.WithK`

Additions to existing modules
-----------------------------

* Properties of non-divisibility in `Algebra.Properties.Magma.Divisibility`:
  ```agda
  ∤-respˡ-≈ : _∤_ Respectsˡ _≈_
  ∤-respʳ-≈ : _∤_ Respectsʳ _≈_
  ∤-resp-≈  : _∤_ Respects₂ _≈_
  ∤∤-sym    : Symmetric _∤∤_
  ∤∤-respˡ-≈ : _∤∤_ Respectsˡ _≈_
  ∤∤-respʳ-≈ : _∤∤_ Respectsʳ _≈_
  ∤∤-resp-≈  : _∤∤_ Respects₂ _≈_
  ```

* In `Algebra.Solver.Ring`
  ```agda
  Env : ℕ → Set _
  Env = Vec Carrier
 ```

* In `Data.List.Base`:
  ```agda
  lookupMaybe : List A → ℕ → Maybe A
  ```

* In `Data.List.Membership.Setoid.Properties`:
  ```agda
  Any-∈-swap    :  Any (_∈ ys) xs → Any (_∈ xs) ys
  All-∉-swap    :  All (_∉ ys) xs → All (_∉ xs) ys
  ∈-map∘filter⁻ : y ∈₂ map f (filter P? xs) → ∃[ x ] x ∈₁ xs × y ≈₂ f x × P x
  ∈-map∘filter⁺ : f Preserves _≈₁_ ⟶ _≈₂_ →
                  ∃[ x ] x ∈₁ xs × y ≈₂ f x × P x →
                  y ∈₂ map f (filter P? xs)
  ∈-concatMap⁺  : Any ((y ∈_) ∘ f) xs → y ∈ concatMap f xs
  ∈-concatMap⁻  : y ∈ concatMap f xs → Any ((y ∈_) ∘ f) xs
  ∉[]           : x ∉ []
  ```

* In `Data.List.Membership.Propositional.Properties`:
  ```agda
  ∈-AllPairs₂   : AllPairs R xs → x ∈ xs → y ∈ xs → x ≡ y ⊎ R x y ⊎ R y x
  ∈-map∘filter⁻ : y ∈ map f (filter P? xs) → (∃[ x ] x ∈ xs × y ≡ f x × P x)
  ∈-map∘filter⁺ : (∃[ x ] x ∈ xs × y ≡ f x × P x) → y ∈ map f (filter P? xs)
  ∈-concatMap⁺  : Any ((y ∈_) ∘ f) xs → y ∈ concatMap f xs
  ∈-concatMap⁻  : y ∈ concatMap f xs → Any ((y ∈_) ∘ f) xs
  ∈-++          : v ∈ xs ++ ys ⇔ (v ∈ xs ⊎ v ∈ ys)
  []∉map∷       : [] ∉ map (x ∷_) xss
  map∷-decomp∈  : (x ∷ xs) ∈ map (y ∷_) xss → x ≡ y × xs ∈ xss
  map∷-decomp   : xs ∈ map (y ∷_) xss → ∃[ ys ] ys ∈ xss × y ∷ ys ≡ xs
  ∈-map∷⁻       : xs ∈ map (x ∷_) xss → x ∈ xs
  ∉[]           : x ∉ []
  ```

* In `Data.List.Membership.Propositional.Properties.WithK`:
  ```agda
  unique∧set⇒bag : Unique xs → Unique ys → xs ∼[ set ] ys → xs ∼[ bag ] ys
  ```

* In `Data.List.Properties`:
  ```agda
  product≢0    : All NonZero ns → NonZero (product ns)
  ∈⇒≤product   : All NonZero ns → n ∈ ns → n ≤ product ns
  concatMap-++ : concatMap f (xs ++ ys) ≡ concatMap f xs ++ concatMap f ys
  ```

* In `Data.List.Relation.Unary.All`:
  ```agda
  search : Decidable P → ∀ xs → All (∁ P) xs ⊎ Any P xs
  ```

* In `Data.List.Relation.Unary.Any.Properties`:
  ```agda
  concatMap⁺ : Any (Any P ∘ f) xs → Any P (concatMap f xs)
  concatMap⁻ : Any P (concatMap f xs) → Any (Any P ∘ f) xs
  ```

* In `Data.List.Relation.Unary.Unique.Setoid.Properties`:
  ```agda
  Unique-dropSnd    : Unique S (x ∷ y ∷ xs) → Unique S (x ∷ xs)
  Unique∷⇒head∉tail : Unique S (x ∷ xs) → x ∉ xs
  ```

* In `Data.List.Relation.Unary.Unique.Propositional.Properties`:
  ```agda
  Unique-dropSnd    : Unique (x ∷ y ∷ xs) → Unique (x ∷ xs)
  Unique∷⇒head∉tail : Unique (x ∷ xs) → x ∉ xs
  ```

* In `Data.List.Relation.Binary.Equality.Setoid`:
  ```agda
  ++⁺ʳ : ∀ xs → ys ≋ zs → xs ++ ys ≋ xs ++ zs
  ++⁺ˡ : ∀ zs → ws ≋ xs → ws ++ zs ≋ xs ++ zs
  ```

* In `Data.List.Relation.Binary.Pointwise`:
  ```agda
  ++⁺ʳ : Reflexive R → ∀ xs → (xs ++_) Preserves (Pointwise R) ⟶ (Pointwise R)
  ++⁺ˡ : Reflexive R → ∀ zs → (_++ zs) Preserves (Pointwise R) ⟶ (Pointwise R)
  ```

* In `Data.List.Relation.Binary.Subset.Propositional.Properties`:
  ```agda
  concatMap⁺ : xs ⊆ ys → concatMap f xs ⊆ concatMap f ys
  ```

* In `Data.List.Relation.Binary.Sublist.Heterogeneous.Properties`:
  ```agda
  Sublist-[]-universal : Universal (Sublist R [])
  ```

* In `Data.List.Relation.Binary.Sublist.Setoid.Properties`:
  ```agda
  []⊆-universal : Universal ([] ⊆_)
  ```

* In `Data.List.Relation.Binary.Disjoint.Setoid.Properties`:
  ```agda
  deduplicate⁺ : Disjoint S xs ys → Disjoint S (deduplicate _≟_ xs) (deduplicate _≟_ ys)
  ∈-dedup      : x ∈ xs ⇔ x ∈ deduplicate _≟_ xs
  ```

* In `Data.List.Relation.Binary.Disjoint.Propositional.Properties`:
  ```agda
  deduplicate⁺ : Disjoint xs ys → Disjoint (deduplicate _≟_ xs) (deduplicate _≟_ ys)
  ∈-dedup      : x ∈ xs ⇔ x ∈ deduplicate _≟_ xs
  ```

* In `Data.List.Relation.Binary.Permutation.Setoid.Properties`:
  ```agda
  ⊈[]    : x ∷ xs ⊈ []
  ⊆∷∧∉⇒⊆ : xs ⊆ y ∷ ys → y ∉ xs → xs ⊆ ys
  ∈∷∧⊆⇒∈ : x ∈ y ∷ xs → xs ⊆ ys → x ∈ y ∷ ys
  ```

* In `Data.List.Relation.Binary.Permutation.Propositional.Properties`:
  ```agda
  ⊈[]    : x ∷ xs ⊈ []
  ⊆∷∧∉⇒⊆ : xs ⊆ y ∷ ys → y ∉ xs → xs ⊆ ys
  ∈∷∧⊆⇒∈ : x ∈ y ∷ xs → xs ⊆ ys → x ∈ y ∷ ys
  ```

* In `Data.List.Relation.Binary.Permutation.Propositional.Properties.WithK`:
  ```agda
  dedup-++-↭ : Disjoint xs ys →
               deduplicate _≟_ (xs ++ ys) ↭ deduplicate _≟_ xs ++ deduplicate _≟_ ys
  ```

* In `Data.Maybe.Properties`:
  ```agda
  maybe′-∘ : ∀ f g → f ∘ (maybe′ g b) ≗ maybe′ (f ∘ g) (f b)
  ```

* New lemmas in `Data.Nat.Properties`:
  ```agda
  m≤n⇒m≤n*o : ∀ o .{{_ : NonZero o}} → m ≤ n → m ≤ n * o
  m≤n⇒m≤o*n : ∀ o .{{_ : NonZero o}} → m ≤ n → m ≤ o * n
  ```

  adjunction between `suc` and `pred`
  ```agda
  suc[m]≤n⇒m≤pred[n] : suc m ≤ n → m ≤ pred n
  m≤pred[n]⇒suc[m]≤n : .{{NonZero n}} → m ≤ pred n → suc m ≤ n
  ```

* New lemma in `Data.Vec.Properties`:
  ```agda
  map-concat : map f (concat xss) ≡ concat (map (map f) xss)
  ```

* In `Data.Vec.Relation.Binary.Equality.DecPropositional`:
  ```agda
  _≡?_ : DecidableEquality (Vec A n)
  ```

* In `Relation.Nullary.Decidable`:
  ```agda
  does-⇔  : A ⇔ B → (a? : Dec A) → (b? : Dec B) → does a? ≡ does b?
  does-≡  : (a? b? : Dec A) → does a? ≡ does b?
  ```

* In `Relation.Unary.Properties`:
  ```agda
  map    : P ≐ Q → Decidable P → Decidable Q
  does-≐ : P ≐ Q → (P? : Decidable P) → (Q? : Decidable Q) → does ∘ P? ≗ does ∘ Q?
  does-≡ : (P? P?′ : Decidable P) → does ∘ P? ≗ does ∘ P?′
  ```
