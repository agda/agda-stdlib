------------------------------------------------------------------------
-- The Agda standard library
--
-- Digits and digit expansions
------------------------------------------------------------------------

module Data.Digit where

open import Data.Nat
open import Data.Fin as Fin using (Fin; zero; suc; toℕ)
open import Relation.Nullary.Decidable
open import Data.Char using (Char)
open import Data.List.Base
open import Data.Product
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Nat.DivMod
open ≤-Reasoning
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Function

------------------------------------------------------------------------
-- Digits

-- Digit b is the type of digits in base b.

Digit : ℕ → Set
Digit b = Fin b

-- Some specific digit kinds.

Decimal = Digit 10
Bit     = Digit 2

-- Some named digits.

0b : Bit
0b = zero

1b : Bit
1b = suc zero

------------------------------------------------------------------------
-- Showing digits

-- The characters used to show the first 16 digits.

digitChars : Vec Char 16
digitChars =
  '0' ∷ '1' ∷ '2' ∷ '3' ∷ '4' ∷ '5' ∷ '6' ∷ '7' ∷ '8' ∷ '9' ∷
  'a' ∷ 'b' ∷ 'c' ∷ 'd' ∷ 'e' ∷ 'f' ∷ []

-- showDigit shows digits in base ≤ 16.

showDigit : ∀ {base} {base≤16 : True (base ≤? 16)} →
            Digit base → Char
showDigit {base≤16 = base≤16} d =
  Vec.lookup (Fin.inject≤ d (toWitness base≤16)) digitChars

------------------------------------------------------------------------
-- Digit expansions

-- fromDigits takes a digit expansion of a natural number, starting
-- with the _least_ significant digit, and returns the corresponding
-- natural number.

fromDigits : ∀ {base} → List (Fin base) → ℕ
fromDigits        []       = 0
fromDigits {base} (d ∷ ds) = toℕ d + fromDigits ds * base
