------------------------------------------------------------------------
-- The Agda standard library
--
-- An explanation about how to use the solver in Tactic.MonoidSolver.
------------------------------------------------------------------------

module README.Tactic.MonoidSolver where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties as Properties using (+-0-monoid; +-comm)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Reasoning.Setoid (setoid ℕ)

open import Tactic.MonoidSolver

-- Unlike the standard monoid solver, the reflective monoid solver is
-- capable to of solving equations without having to specify the
-- equation itself in the proof.

example₁ : ∀ x y z → (x + y) + z ≡ x + (y + z) + 0
example₁ x y z = solve +-0-monoid

-- The solver can also be used in equational reasoning.

example₂ : ∀ x y z → z + (x + y) ≡ x + (y + z) + 0
example₂ x y z = begin
  z + (x + y)      ≈⟨ +-comm z (x + y) ⟩
  (x + y) + z      ≈⟨ solve +-0-monoid ⟩
  x + (y + z) + 0  ∎
