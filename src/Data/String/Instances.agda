------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for strings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.String.Instances where

open import Data.String.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  String-≡-isDecEquivalence = isDecEquivalence _≟_
