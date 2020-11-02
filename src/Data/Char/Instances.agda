------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for characters
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Char.Instances where

open import Data.Char.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  Char-≡-isDecEquivalence = isDecEquivalence _≟_
