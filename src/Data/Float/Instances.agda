------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for floating point numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Float.Instances where

open import Data.Float.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  float≡-isDecEquivalence = isDecEquivalence _≟_
