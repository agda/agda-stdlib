------------------------------------------------------------------------
-- The Agda standard library
--
-- An explanation about how to use the solver in
-- Algebra.Solver.Monoid.Reflection.
------------------------------------------------------------------------

module README.Solvers.ReflectiveMonoid where

open import Data.Nat as Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties as Properties using (+-0-monoid; +-comm)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Reasoning.Setoid (setoid ℕ)

open import Algebra.Solver.Monoid.Reflection

-- Unlike the standard monoid solver, the reflective monoid solver is
-- capable to of solving equations without having to specify the
-- equation itself in the proof.

example₁ : ∀ x y z → (x + y) + z ≡ x + (y + z) + 0
example₁ x y z = solve +-0-monoid

-- The solver can also be used in equational reasoning, but only
-- inside of the special _≈!⟨_⟩_ operator. The reasons for this is
-- that the standard _≈⟨_⟩_ combinator infers the LHS of the equational
-- step from the RHS + the type of the proof, whereas _≈!⟨_⟩_ infers
-- the type of the proof from the LHS + RHS of the equational step.

example₂ : ∀ x y z → z + (x + y) ≡ x + (y + z) + 0
example₂ x y z = begin
  z + (x + y)      ≈⟨ +-comm z (x + y) ⟩
  (x + y) + z      ≈!⟨ solve +-0-monoid ⟩
  x + (y + z) + 0  ∎
