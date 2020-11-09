------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for signs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sign.Instances where

open import Data.Sign.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  Sign-≡-isDecEquivalence = isDecEquivalence _≟_
