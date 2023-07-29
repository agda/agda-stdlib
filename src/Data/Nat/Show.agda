------------------------------------------------------------------------
-- The Agda standard library
--
-- Showing natural numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Show where

open import Data.Bool.Base using (_∧_)
open import Data.Char.Base as Char using (Char)
open import Data.Digit using (showDigit; toDigits; toNatDigits)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Effectful using (module TraversableA)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; _<∣>_; when)
import Data.Maybe.Effectful as Maybe
open import Data.Nat
open import Data.Product.Base using (proj₁)
open import Data.String.Base as String using (String; fromList; toList)
open import Function.Base using (_∘′_; _∘_)
open import Relation.Nullary.Decidable using (True)

------------------------------------------------------------------------
-- Read

readMaybe : ∀ base {base≤16 : True (base ≤? 16)} → String → Maybe ℕ
readMaybe _ "" = nothing
readMaybe base = Maybe.map convert
              ∘′ TraversableA.mapA Maybe.applicative readDigit
              ∘′ toList

  where

    convert : List ℕ → ℕ
    convert = List.foldl (λ acc d → base * acc + d) 0

    char0 = Char.toℕ '0'
    char9 = Char.toℕ '9'
    chara = Char.toℕ 'a'
    charf = Char.toℕ 'f'

    readDigit : Char → Maybe ℕ
    readDigit c = digit Maybe.>>= λ n → when (n <ᵇ base) n where

      charc = Char.toℕ c

      dec = when ((char0 ≤ᵇ charc) ∧ (charc ≤ᵇ char9)) (charc ∸ char0)
      hex = when ((chara ≤ᵇ charc) ∧ (charc ≤ᵇ charf)) (10 + charc ∸ chara)
      digit = dec <∣> hex

------------------------------------------------------------------------
-- Show

-- Decimal notation
-- Time complexity is O(log₁₀(n))

toDigitChar : ℕ → Char
toDigitChar n = Char.fromℕ (n + Char.toℕ '0')

toDecimalChars : ℕ → List Char
toDecimalChars = List.map toDigitChar ∘′ toNatDigits 10

show : ℕ → String
show = fromList ∘′ toDecimalChars

-- Arbitrary base betwen 2 & 16.
-- Warning: when compiled the time complexity of `showInBase b n` is
-- O(n) instead of the expected O(log(n)).

charsInBase : (base : ℕ)
              {base≥2 : True (2 ≤? base)}
              {base≤16 : True (base ≤? 16)} →
              ℕ → List Char
charsInBase base {base≥2} {base≤16} = List.map (showDigit {base≤16 = base≤16})
                                    ∘ List.reverse
                                    ∘ proj₁
                                    ∘ toDigits base {base≥2 = base≥2}

showInBase : (base : ℕ)
             {base≥2 : True (2 ≤? base)}
             {base≤16 : True (base ≤? 16)} →
             ℕ → String
showInBase base {base≥2} {base≤16} = fromList
                                   ∘ charsInBase base {base≥2} {base≤16}
