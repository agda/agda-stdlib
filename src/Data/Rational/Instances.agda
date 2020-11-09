------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Instances where

open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  ℚ-≡-isDecEquivalence = isDecEquivalence _≟_
  ℚ-≤-isDecTotalOrder = ≤-isDecTotalOrder
