------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational where

------------------------------------------------------------------------
-- Publicly re-export contents of core module and queries

open import Data.Rational.Base public
open import Data.Rational.Properties public
  using (_≟_; _≤?_; _<?_)

------------------------------------------------------------------------
-- Deprecated

-- Version 1.0

open import Data.Rational.Properties public
  using (drop-*≤*; ≃⇒≡; ≡⇒≃)

-- Version 1.5

import Data.Integer.Show as ℤ
open import Data.String using (String; _++_)

show : ℚ → String
show p = ℤ.show (↥ p) ++ "/" ++ ℤ.show (↧ p)

{-# WARNING_ON_USAGE show
"Warning: show was deprecated in v1.5.
Please use Data.Rational.Show's show instead."
#-}
