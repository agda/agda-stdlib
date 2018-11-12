------------------------------------------------------------------------
-- The Agda standard library
--
-- Instantiates the natural coefficients ring solver, using coefficient
-- equality induced by ℕ.
--
-- This is sufficient for proving equalities that are independent of the
-- characteristic.  In particular, this is enough for equalities in rings of
-- characteristic 0.
------------------------------------------------------------------------

open import Algebra

module Algebra.Solver.Ring.NaturalCoefficients.Default
         {r₁ r₂} (R : CommutativeSemiring r₁ r₂) where

import Algebra.Operations.Semiring as SemiringOps
open import Data.Maybe.Base using (Maybe; map)
open import Data.Nat using (_≟_)
open import Relation.Binary.Consequences using (dec⟶weaklyDec)
import Relation.Binary.PropositionalEquality as P

open CommutativeSemiring R
open SemiringOps semiring

private
  dec : ∀ m n → Maybe (m × 1# ≈ n × 1#)
  dec m n = map (λ { P.refl → refl }) (dec⟶weaklyDec _≟_ m n)

open import Algebra.Solver.Ring.NaturalCoefficients R dec public
