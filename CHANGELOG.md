Version 2.2-dev
===============

The library has been tested using Agda 2.6.4.3.

Highlights
----------

Bug-fixes
---------

Non-backwards compatible changes
--------------------------------

Minor improvements
------------------

Deprecated modules
------------------

Deprecated names
----------------

* In `Algebra.Solver.CommutativeMonoid`:
  ```agda
  normalise-correct  ↦  Algebra.Solver.CommutativeMonoid.Normal.correct
  ```

* In `Algebra.Solver.IdempotentCommutativeMonoid`:
  ```agda
  flip12             ↦  Algebra.Properties.CommutativeSemigroup.xy∙z≈y∙xz
  normalise-correct  ↦  Algebra.Solver.IdempotentCommutativeMonoid.Normal.correct
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
  a single `Tactic` module API based on the existing `Expr`, and
  a common `Normal`-form API:
  ```agda
  Algebra.Solver.CommutativeMonoid.Normal
  Algebra.Solver.IdempotentCommutativeMonoid.Normal
  Algebra.Solver.Monoid.Expression
  Algebra.Solver.Monoid.Normal
  Algebra.Solver.Monoid.Tactic
  ```

Additions to existing modules
-----------------------------

* In `Algebra.Solver.Ring`
  ```agda
  Env : ℕ → Set _
  Env = Vec Carrier
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

* New lemma in `Data.Vec.Properties`:
  ```agda
  map-concat : map f (concat xss) ≡ concat (map (map f) xss)
  ```

* In `Data.Vec.Relation.Binary.Equality.DecPropositional`:
  ```agda
  _≡?_ : DecidableEquality (Vec A n)
  ```
