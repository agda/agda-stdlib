Version 2.2-dev
===============

The library has been tested using Agda 2.6.4.3.

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

Additions to existing modules
-----------------------------

* In `Data.Product.Function.Dependent.Propositional`:
  ```agda
  cong′ : ∀ {k} → (∀ {x} → A x ∼[ k ] B x) → Σ I A ∼[ k ] Σ I B
  ```

* In `Data.List.Properties`:
  ```agda
  product≢0 : All NonZero ns → NonZero (product ns)
  ∈⇒≤product : All NonZero ns → n ∈ ns → n ≤ product ns
  ```

* In `Data.List.Relation.Unary.All`:
  ```agda
  search : Decidable P → ∀ xs → All (∁ P) xs ⊎ Any P xs
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

* In `Function.Related.TypeIsomorphisms`:
  ```agda
  Σ-distribˡ-⊎ : {P : A → Set a} {Q : A → Set b} → (∃ λ a → P a ⊎ Q a) ↔ (∃ P ⊎ ∃ Q)
  Σ-distribʳ-⊎ : {P : Set a} {Q : Set b} {R : P ⊎ Q → Set c} → (Σ (P ⊎ Q) R) ↔ (Σ P (R ∘ inj₁) ⊎ Σ Q (R ∘ inj₂))
  ×-distribˡ-⊎′ : (A × (B ⊎ C)) ↔ (A × B ⊎ A × C)
  ×-distribʳ-⊎′ : ((A ⊎ B) × C) ↔ (A × C ⊎ B × C)
  ∃-≡ : ∀ (P : A → Set b) {x} → P x ↔ (∃[ y ] y ≡ x × P y)
 ```

* In `Relation.Nullary.Decidable`:
  ```agda
  does-⇔  : A ⇔ B → (a? : Dec A) → (b? : Dec B) → does a? ≡ does b?
  does-≡  : (a? b? : Dec A) → does a? ≡ does b?
  ```

* In `Relation.Nullary.Properties`:
  ```agda
  map    : P ≐ Q → Decidable P → Decidable Q
  does-≐ : P ≐ Q → (P? : Decidable P) → (Q? : Decidable Q) → does ∘ P? ≗ does ∘ Q?
  does-≡ : (P? P?′ : Decidable P) → does ∘ P? ≗ does ∘ P?′
  ```
