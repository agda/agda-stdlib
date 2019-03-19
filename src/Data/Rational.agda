------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational where

open import Data.Integer as ℤ using (ℤ; +_)
open import Data.String using (String; _++_)

------------------------------------------------------------------------
-- Publicly re-export contents of core module

open import Data.Rational.Base public

------------------------------------------------------------------------
-- Publicly re-export queries

open import Data.Nat.Properties public
  using (_≟_; _≤?_)

------------------------------------------------------------------------
-- Publicly re-export contents of core module

show : ℚ → String
show p = ℤ.show (↥ p) ++ "/" ++ ℤ.show (↧ p)

------------------------------------------------------------------------------
-- Some constants

0ℚ : ℚ
0ℚ = + 0 ÷ 1

1ℚ : ℚ
1ℚ = + 1 ÷ 1

½ : ℚ
½ = + 1 ÷ 2

-½ : ℚ
-½ = - ½

------------------------------------------------------------------------
-- Deprecated

-- Version 1.0

open import Data.Rational.Properties public
  using (drop-*≤*; ≃⇒≡; ≡⇒≃)
