------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing unnormalised rational numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Unnormalised.Show where

import Data.Integer.Show as ℤ
open import Data.Rational.Unnormalised.Base
open import Data.String.Base using (String; _++_)

show : ℚᵘ → String
show p = ℤ.show (↥ p) ++ "/" ++ ℤ.show (↧ p)
