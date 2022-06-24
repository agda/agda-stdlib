------------------------------------------------------------------------
-- The Agda standard library
--
-- Postulated Real numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.PostulatedReal where

------------------------------------------------------------------------
-- Publicly re-export contents of core module and queries

open import Data.PostulatedReal.Base public
open import Data.PostulatedReal.Properties.Core public
  using (_≟_; _≤?_; _<?_)

infixl 7 _⊓_
infixl 6 _⊔_

-- max
_⊔_ : (x y : ℝ) → ℝ
x ⊔ y = {!   !} --if x ≤ᵇ y then x else y

-- min
_⊓_ : (x y : ℝ) → ℝ
x ⊓ y = {!   !} --if x ≤ᵇ y then x else y

-- absolute value
∣_∣ : ℝ → ℝ
∣ x ∣ = {!   !}

