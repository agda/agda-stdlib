------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for words
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Word64.Instances where

open import Data.Word64.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  Word64-≡-isDecEquivalence = isDecEquivalence _≟_
