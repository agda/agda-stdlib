------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for words
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Word.Instances where

open import Data.Word.Properties
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  Word-≡-isDecEquivalence = isDecEquivalence _≟_
