------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for signs
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Sign.Instances where

open import Data.Sign.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  Sign-≡-isDecEquivalence = isDecEquivalence _≟_
