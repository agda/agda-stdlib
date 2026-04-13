------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for binary natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Binary.Instances where

open import Data.Nat.Binary.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  ℕᵇ-≡-isDecEquivalence = isDecEquivalence _≟_
