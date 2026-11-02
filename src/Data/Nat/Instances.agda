------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Instances where

open import Data.Char using (isDigit)
open import Data.List.Base using (_∷_; _++_; spanᵇ)
open import Data.Maybe using (_>>=_; just)
open import Data.Nat.Base using (ℕ; _≤ᵇ_)
open import Data.Nat.Properties using (≤-isDecTotalOrder; _≡?_)
open import Data.Nat.Show using (readMaybe) renaming (show to showℕ)
open import Data.Product using (_,_)
open import Data.String.Base using (toList; fromList)
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Text.Read using (Read)
open import Text.Write using (Write)

instance
  ℕ-≡-isDecEquivalence = isDecEquivalence _≡?_
  ℕ-≤-isDecTotalOrder = ≤-isDecTotalOrder

instance
  open Write
  NatWrite : Write ℕ
  NatWrite .writesPrecList _ n str = showℕ n ∷ str

instance
  open Read {{...}}
  NatRead : Read ℕ
  NatRead .readsPrecList prec str = do
    let (digits , leftover) = spanᵇ isDigit str
    num ← readMaybe 10 (fromList digits)
    just (num , leftover)
