------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing rational numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Show where

open import Data.Integer.Base using (ℤ; +_; ∣_∣)
import Data.Integer.Show as ℤ using (show)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Show using (toDigitChar)
open import Data.Product.Base using (_×_; _,_)
open import Data.Rational.Base
  using (ℚ; ↥_; ↧_; _/_; _*_; truncate; fracPart)
open import Data.String.Base using (String; _++_)
open import Data.String using (fromVec)
open import Data.Vec.Base using (Vec; []; _∷_; map)

show : ℚ → String
show p = ℤ.show (↥ p) ++ "/" ++ ℤ.show (↧ p)

-- The integer part of q,
-- followed by the first n digits of its decimal representation
atPrecision : (n : ℕ) → ℚ → ℤ × Vec ℕ n
atPrecision n q = (truncate q , decimalPart n ((+ 10 / 1) * (fracPart q)))
  where
  decimalPart : (n : ℕ) → ℚ → Vec ℕ n
  decimalPart zero q = []
-- fracPart q is a (non-negative) proper fraction,
-- and 0 ≤ num < den implies 0 ≤ 10 num/den < 10,
-- so everything but position 0 is a proper digit
  decimalPart (suc n) q
    = ∣ truncate q ∣ ∷ decimalPart n ((+ 10 / 1) * (fracPart q))

showAtPrecision : ℕ → ℚ → String
showAtPrecision n q with atPrecision n q
... | (int , dec) = ℤ.show int ++ "." ++ (fromVec (map toDigitChar dec))
