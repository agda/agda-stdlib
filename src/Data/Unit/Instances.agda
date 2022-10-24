------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for the unit type
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Unit.Instances where

open import Data.Unit.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  ⊤-≡-isDecEquivalence = isDecEquivalence _≟_
  ⊤-≤-isDecTotalOrder = ≡-isDecTotalOrder
