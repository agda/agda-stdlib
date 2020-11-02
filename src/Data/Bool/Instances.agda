------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for booleans
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Bool.Instances where

open import Data.Bool.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  bool≡-isDecEquivalence = isDecEquivalence _≟_
