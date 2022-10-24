------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for parities
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Parity.Instances where

open import Data.Parity.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  Parity-≡-isDecEquivalence = ≡-isDecEquivalence
