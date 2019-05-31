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
-- Publicly re-export contents of core module and queries

open import Data.Rational.Base public
open import Data.Rational.Properties public
  using (_≟_; _≤?_; _<?_)

------------------------------------------------------------------------
-- Method for displaying rationals

show : ℚ → String
show p = ℤ.show (↥ p) ++ "/" ++ ℤ.show (↧ p)

------------------------------------------------------------------------
-- Deprecated

-- Version 1.0

open import Data.Rational.Properties public
  using (drop-*≤*; ≃⇒≡; ≡⇒≃)
