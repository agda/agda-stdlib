------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles of parameters for passing to the Ring Solver
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This module packages up all the stuff that's passed to the other
-- modules in a convenient form.

module Tactic.RingSolver.Core.Polynomial.Parameters where

open import Algebra.Bundles using (RawRing)
open import Data.Bool.Base using (Bool; T)
open import Function
open import Level
open import Relation.Unary
open import Tactic.RingSolver.Core.AlmostCommutativeRing

-- This record stores all the stuff we need for the coefficients:
--
--  * A raw ring
--  * A (decidable) predicate on "zeroeness"
--
-- It's used for defining the operations on the Horner normal form.
record RawCoeff ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    rawRing : RawRing ℓ₁ ℓ₂
    isZero  : RawRing.Carrier rawRing → Bool

  open RawRing rawRing public

-- This record stores the full information we need for converting
-- to the final ring.
record Homomorphism ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    from : RawCoeff ℓ₁ ℓ₂
    to   : AlmostCommutativeRing ℓ₃ ℓ₄

  module Raw = RawCoeff from
  open AlmostCommutativeRing to public

  field
    morphism : Raw.rawRing -Raw-AlmostCommutative⟶ to
  open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧ᵣ) public
  field
    Zero-C⟶Zero-R : ∀ x → T (Raw.isZero x) → 0# ≈  ⟦ x ⟧ᵣ
