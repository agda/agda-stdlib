------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of showing natural numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Digit.Properties using (toDigits-injective; showDigit-injective)
import Data.List.Properties as Listₚ
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≤?_)
open import Data.Nat.Show using (charsInBase)
open import Function.Base using (_∘_)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

module Data.Nat.Show.Properties where

module _ (base : ℕ) {base≥2 : True (2 ≤? base)} {base≤16 : True (base ≤? 16)} where

  private
    charsInBase-base         = charsInBase base {base≥2} {base≤16}
    toDigits-injective-base  = toDigits-injective base {base≥2} {base≥2}
    showDigit-injective-base = showDigit-injective base {base≤16} {base≤16}

  charsInBase-injective : ∀ n m →  charsInBase-base n ≡ charsInBase-base m → n ≡ m
  charsInBase-injective n m = toDigits-injective-base _ _
                            ∘ Listₚ.reverse-injective
                            ∘ Listₚ.map-injective (showDigit-injective-base _ _)
