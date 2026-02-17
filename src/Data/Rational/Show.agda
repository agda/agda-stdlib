------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing rational numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Show where

import Data.Integer.Show as ℤ using (show)
open import Data.Rational.Base
  using (ℚ; ↥_; ↧_; _/_; _*_; truncate; fracPart)
open import Data.String.Base using (String; _++_; concat)
open import Data.Nat using (ℕ; suc)
open import Data.Integer using (ℤ; +_)
open import Data.Vec using (Vec; []; _∷_; map; toList)

show : ℚ → String
show p = ℤ.show (↥ p) ++ "/" ++ ℤ.show (↧ p)

-- The integer part of q,
-- followed by the first n digits of its decimal representation
atPrecision : (n : ℕ) → ℚ → Vec ℤ (suc n)
atPrecision ℕ.zero q = (truncate q) ∷ []
-- fracPart q is a (non-negative) proper fraction,
-- and 0 ≤ num < den implies 0 ≤ 10 num/den < 10,
-- so everything but position 0 is a proper digit
atPrecision (ℕ.suc n) q
  = (truncate q) ∷ (atPrecision n ((+ 10 / 1) * (fracPart q)))

showAtPrecision : ℕ → ℚ → String
showAtPrecision n q with atPrecision n q
... | int ∷ dec = ℤ.show int ++ "." ++ concat (toList (map ℤ.show dec))
