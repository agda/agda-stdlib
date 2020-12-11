------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Instances where

open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  ℕ-≡-isDecEquivalence = isDecEquivalence _≟_
  ℕ-≤-isDecTotalOrder = ≤-isDecTotalOrder
