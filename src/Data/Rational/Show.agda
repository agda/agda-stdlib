------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Show where

import Data.Integer.Show as ℤ
open import Data.Rational.Base
open import Data.String.Base using (String; _++_)

show : ℚ → String
show p = ℤ.show (↥ p) ++ "/" ++ ℤ.show (↧ p)
