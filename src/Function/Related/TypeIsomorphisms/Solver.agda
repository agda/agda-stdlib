------------------------------------------------------------------------
-- The Agda standard library
--
-- Automatic solver for equations over product and sum types
--
-- See examples at the bottom of the file for how to use this solver
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Related.TypeIsomorphisms.Solver where

open import Algebra using (CommutativeSemiring)
import Algebra.Solver.Ring.NaturalCoefficients.Default
  using (solve; con; _:*_; _:+_; _:=_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product.Base using (_×_)
open import Data.Sum.Base using (_⊎_)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level)
open import Function.Bundles using (_↔_)
open import Function.Properties.Inverse using (↔-refl)
open import Function.Related.Propositional as Related
open import Function.Related.TypeIsomorphisms using (×-⊎-commutativeSemiring)

------------------------------------------------------------------------
-- The solver

module ×-⊎-Solver (k : SymmetricKind) {ℓ} =
  Algebra.Solver.Ring.NaturalCoefficients.Default
    (×-⊎-commutativeSemiring k ℓ)

------------------------------------------------------------------------
-- Tests

private

  -- A test of the solver above.

  test : {ℓ : Level} (A B C : Set ℓ) →
         (⊤ × A × (B ⊎ C)) ↔ (A × B ⊎ C × (⊥ ⊎ A))
  test = solve 3 (λ A B C → con 1 :* (A :* (B :+ C)) :=
                            A :* B :+ C :* (con 0 :+ A))
                 ↔-refl
    where open ×-⊎-Solver bijection
