------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of GCD.
------------------------------------------------------------------------

-- You're unlikely to want to use this module directly. Instead you
-- probably want to be importing the appropriate module from
-- `Algebra.Properties.CancellativeCommutativeSemiring`.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core using (Op₂)
open import Data.Product using (proj₁; proj₂)
open import Level using (_⊔_)
open import Relation.Binary using (Rel)

module Algebra.GCD {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_*_ : Op₂ A) where

open import Algebra.Divisibility _≈_ _*_

------------------------------------------------------------------------------
-- Definitions

record GCD (arg1 arg2 : A) :  Set (a ⊔ ℓ) where      -- a result of gcd
  constructor gcdᶜ
  -- Greatest common divisor.

  field
    value    : A                  -- the proper gcd value
    divides₁ : value ∣ arg1
    divides₂ : value ∣ arg2
    greatest : ∀ {x} → (x ∣ arg1) → (x ∣ arg2) → (x ∣ value)

  quot₁ quot₂ : A
  quot₁ = proj₁ divides₁
  quot₂ = proj₁ divides₂

  quot₁*value≈arg1 : (quot₁ * value) ≈ arg1
  quot₁*value≈arg1 = proj₂ divides₁

  quot₂*value≈arg2 : (quot₂ * value) ≈ arg2
  quot₂*value≈arg2 = proj₂ divides₂
