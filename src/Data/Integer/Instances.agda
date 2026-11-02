------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for integers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.Instances where

open import Data.Integer.Base using (ℤ)
open import Data.Integer.Properties using (_≡?_; ≤-isDecTotalOrder)
open import Data.Integer.Show using () renaming (show to showℤ)
open import Data.List.Base using (_∷_)
open import Data.String.Base using (toList)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)

open import Text.Write using (Write)

instance
  ℤ-≡-isDecEquivalence = isDecEquivalence _≡?_
  ℤ-≤-isDecTotalOrder = ≤-isDecTotalOrder

instance
  open Write
  IntWrite : Write ℤ
  IntWrite .writesPrecList _ i str = showℤ i ∷ str
