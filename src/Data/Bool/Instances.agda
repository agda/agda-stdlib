------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for booleans
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Bool.Instances where

open import Data.Bool.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  Bool-≡-isDecEquivalence = isDecEquivalence _≟_
  Bool-≤-isDecTotalOrder = ≤-isDecTotalOrder
