------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Instances where

open import Data.List.Base using (_++_)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (≤-isDecTotalOrder; _≡?_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String.Base using (toList)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Text.Show using (Show)

instance
  ℕ-≡-isDecEquivalence = isDecEquivalence _≡?_
  ℕ-≤-isDecTotalOrder = ≤-isDecTotalOrder

instance
  open Show
  NatShow : Show ℕ
  NatShow .showsPrecList _ n str = (toList (showℕ n)) ++ str
