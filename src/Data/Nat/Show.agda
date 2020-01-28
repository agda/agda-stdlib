------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing natural numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Show where

open import Data.Char as Char using (Char)
open import Data.Digit using (showDigit; toDigits; toNatDigits)
open import Function using (_∘_; _$_)
open import Data.List.Base using (List; []; _∷_; map; reverse)
open import Data.Nat
open import Data.Product using (proj₁)
open import Data.String as String using (String)
open import Relation.Nullary.Decidable using (True)

------------------------------------------------------------------------
-- Conversion from unary representation to the representation by the
-- given base.

toDigitChar : (n : ℕ) → Char
toDigitChar n = Char.fromℕ (n + (Char.toℕ '0'))

toDecimalChars : ℕ → List Char
toDecimalChars = map toDigitChar ∘ toNatDigits 10

------------------------------------------------------------------------
-- Show

-- Time complexity is O(log₁₀(n))

show : ℕ → String
show = String.fromList ∘ toDecimalChars

-- Warning: when compiled the time complexity of `showInBase b n` is
-- O(n) instead of the expected O(log(n)).

showInBase : (base : ℕ)
             {base≥2 : True (2 ≤? base)}
             {base≤16 : True (base ≤? 16)} →
             ℕ → String
showInBase base {base≥2} {base≤16} n =
  String.fromList $
  map (showDigit {base≤16 = base≤16}) $
  reverse $
  proj₁ $ toDigits base {base≥2 = base≥2} n
