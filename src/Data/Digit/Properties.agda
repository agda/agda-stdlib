------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of digits and digit expansions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Digit
import Data.Char.Properties as Charₚ
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≤?_)
open import Data.Fin.Properties using (inject≤-injective)
open import Data.Product using (_,_; proj₁)
open import Data.Vec.Relation.Unary.Unique.Propositional using (Unique)
import Data.Vec.Relation.Unary.Unique.Propositional.Properties as Uniqueₚ
open import Data.Vec.Relation.Unary.AllPairs using (allPairs?)
open import Relation.Nullary.Decidable using (True; from-yes)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Function using (_∘_)

module Data.Digit.Properties where

digitCharsUnique : Unique digitChars
digitCharsUnique = from-yes (allPairs? (λ x y → ¬? (x Charₚ.≟ y)) digitChars)

module _ (base : ℕ) where
  module _ {base≥2 base≥2′ : True (2 ≤? base)} where
    toDigits-injective : ∀ n m → proj₁ (toDigits base {base≥2} n) ≡ proj₁ (toDigits base {base≥2′} m) → n ≡ m
    toDigits-injective n m eq with toDigits base {base≥2} n | toDigits base {base≥2′} m
    toDigits-injective ._ ._ refl | _ , refl | ._ , refl = refl

  module _ {base≤16 base≤16′ : True (base ≤? 16)} where
    showDigit-injective : (n m : Digit base) → showDigit {base} {base≤16} n ≡ showDigit {base} {base≤16′} m → n ≡ m
    showDigit-injective n m = inject≤-injective _ _ n m ∘ Uniqueₚ.lookup-injective digitCharsUnique _ _
