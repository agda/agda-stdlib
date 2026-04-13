------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for strings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String.Instances where

open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

instance
  String-≡-isDecEquivalence = isDecEquivalence _≟_
