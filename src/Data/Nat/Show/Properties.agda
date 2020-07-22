------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of showing natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Digit using (showDigit; toDigits)
open import Data.Digit.Properties using (toDigits-injective; showDigit-injective)
open import Function using (_∘_)
import Data.List.Properties as Listₚ
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary.Decidable using (True)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat.Show using (charsInBase)

module Data.Nat.Show.Properties where

module _ (base : ℕ) {base≥2 : True (2 ≤? base)} {base≤16 : True (base ≤? 16)} where

  charsInBase-injective : ∀ n m → charsInBase base {base≥2} {base≤16} n ≡ charsInBase base {base≥2} {base≤16} m → n ≡ m
  charsInBase-injective n m = toDigits-injective base {base≥2} _ _
                            ∘ Listₚ.reverse-injective
                            ∘ Listₚ.map-injective (showDigit-injective _ _ _)
