------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for floating point numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Float.Instances where

open import Data.Float.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  Float-≡-isDecEquivalence = isDecEquivalence _≟_
