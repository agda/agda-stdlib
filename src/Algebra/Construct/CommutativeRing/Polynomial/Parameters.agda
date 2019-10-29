{-# OPTIONS --without-K --safe #-}

-- This module packages up all the stuff that's passed to the other
-- modules in a convenient form.

module Algebra.Construct.CommutativeRing.Polynomial.Parameters where

open import Function
open import Algebra
open import Relation.Unary
open import Level
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Data.Bool using (Bool; T)

-- This record stores all the stuff we need for the coefficients:
--
--  * A raw ring
--  * A (decidable) predicate on "zeroeness"
--
-- It's used for defining the operations on the horner normal form.
record RawCoeff ℓ : Set (suc ℓ) where
  field
    rawRing : RawRing ℓ
    Zero-C  : RawRing.Carrier rawRing → Bool

  open RawRing rawRing public

-- This record stores the full information we need for converting
-- to the final ring.
record Homomorphism ℓ₁ ℓ₂ ℓ₃ : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    from : RawCoeff ℓ₁
  module Raw = RawCoeff from
  field
    to     : AlmostCommutativeRing ℓ₂ ℓ₃
    morphism : Raw.rawRing -Raw-AlmostCommutative⟶ to
  open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧ᵣ) public
  open AlmostCommutativeRing to public
  field
    Zero-C⟶Zero-R : ∀ x → T (Raw.Zero-C x) → 0# ≈  ⟦ x ⟧ᵣ
