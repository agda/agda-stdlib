------------------------------------------------------------------------
-- The Agda standard library
--
-- An explanation about how to use the solver in
-- Algebra.Solver.Monoid.Reflection.
------------------------------------------------------------------------
module README.SolverExample where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties as Properties using (+-0-monoid; +-comm)
open import Algebra.Solver.Monoid.Reflection
open import Relation.Binary.PropositionalEquality

open import Relation.Binary.Reasoning.Setoid (setoid ℕ)

example₁ : ∀ x y z → (x + y) + z ≡ x + (y + z) + 0
example₁ x y z = solve +-0-monoid

example₂ : ∀ x y z → z + (x + y) ≡ x + (y + z) + 0
example₂ x y z = begin
  z + (x + y) ≈⟨ +-comm z (x + y) ⟩
  (x + y) + z ≈!⟨ solve +-0-monoid ⟩
  x + (y + z) + 0 ∎
