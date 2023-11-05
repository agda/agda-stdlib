------------------------------------------------------------------------
-- The Agda standard library
--
-- An explanation about how to use the solver in Tactic.MonoidSolver.
------------------------------------------------------------------------

open import Algebra

module README.Tactic.MonoidSolver {a ℓ} (M : Monoid a ℓ) where

open Monoid M

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties as Properties using (+-0-monoid; +-comm)
open import Relation.Binary.Reasoning.Setoid setoid

open import Tactic.MonoidSolver using (solve; solve-macro)

-- The monoid solver is capable to of solving equations without having
-- to specify the equation itself in the proof.

example₁ : ∀ x y z → (x ∙ y) ∙ z ≈ x ∙ (y ∙ z) ∙ ε
example₁ x y z = solve M

-- The solver can also be used in equational reasoning.

example₂ : ∀ w x y z → w ≈ x → (w ∙ y) ∙ z ≈ x ∙ (y ∙ z) ∙ ε
example₂ w x y z w≈x = begin
  (w ∙ y) ∙ z      ≈⟨ ∙-congʳ (∙-congʳ w≈x) ⟩
  (x ∙ y) ∙ z      ≈⟨ solve M ⟩
  x ∙ (y ∙ z) ∙ ε  ∎
