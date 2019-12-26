{-# OPTIONS --without-K --safe #-}

-- This module packages up all the stuff that's passed to the other
-- modules in a convenient form.

module Algebra.Construct.Polynomial.Parameters where

open import Algebra
open import Algebra.Morphism
open import Data.Bool using (Bool; T)
open import Function
open import Level
open import Relation.Unary

-- This record stores all the stuff we need for the coefficients:
--
--  * A raw ring
--  * A (decidable) predicate on "zeroeness"
--
-- It's used for defining the operations on the horner normal form.
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
  module Raw = RawCoeff from
  field
    to       : AlmostCommutativeRing ℓ₃ ℓ₄
    morphism : Raw.rawRing -Raw-AlmostCommutative⟶ to
  open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧ᵣ) public
  open AlmostCommutativeRing to public
  field
    Zero-C⟶Zero-R : ∀ x → T (Raw.isZero x) → 0# ≈  ⟦ x ⟧ᵣ
