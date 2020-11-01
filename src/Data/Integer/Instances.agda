------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for integers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.Instances where

open import Data.Integer.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  ≡-isDecEquivalence-Integer = isDecEquivalence _≟_
