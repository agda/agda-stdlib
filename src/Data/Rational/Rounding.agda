------------------------------------------------------------------------
-- The Agda standard library
--
-- Rounding rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Rounding where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Base using (ℕ)
open import Data.Integer.Base as ℤ using (ℤ)
open import Data.Integer.DivMod using (_div_)
open import Data.Rational.Base
  using (ℚ; ↥_; ↧_; _≤ᵇ_; -_; _/_; 0ℚ; ½; _+_; _-_)

------------------------------------------------------------------------
-- ROUNDING FUNCTIONS

-- Floor (round towards -∞)
floor : ℚ → ℤ
floor p = (↥ p) div (↧ p)

-- Ceiling (round towards +∞)
ceiling : ℚ → ℤ
ceiling p = ℤ.- floor (- p)

-- Truncate  (round towards 0)
truncate : ℚ → ℤ
truncate p with (p ≤ᵇ 0ℚ)
...           | true  = ceiling p
...           | false = floor p

-- Round (to nearest integer)
round : ℚ → ℤ
round p = floor (p + ½)

-- Fractional part (remainder after floor)
fracPart : ℚ → ℚ
fracPart p = p - floor p / 1

--- Extra notations  ⌊ ⌋ floor,  ⌈ ⌉ ceiling,  [] truncate
⌊_⌋ ⌈_⌉ [_] : ℚ → ℤ
⌊ p ⌋ = floor p
⌈ p ⌉ = ceiling p
[ p ] = truncate p