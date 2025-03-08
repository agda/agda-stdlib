------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing rational numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Show where

import Data.Integer.Show as ℤ using (show)
open import Data.Rational.Base using (ℚ; ↥_; ↧_)
open import Data.String.Base using (String; _++_)

show : ℚ → String
show p = ℤ.show (↥ p) ++ "/" ++ ℤ.show (↧ p)
