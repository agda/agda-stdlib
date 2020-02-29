------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational Literals
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Literals where

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Data.Unit
open import Data.Nat.Base
open import Data.Nat.Coprimality
open import Data.Integer.Base
open import Data.Rational hiding (-_)

fromℤ : ℤ → ℚ
fromℤ z = record
  { numerator     = z
  ; denominator-1 = zero
  ; isCoprime     = sym (1-coprimeTo ∣ z ∣)
  }

number : Number ℚ
number = record
  { Constraint = λ _ → ⊤
  ; fromNat    = λ n → fromℤ (+ n)
  }

negative : Negative ℚ
negative = record
  { Constraint = λ _ → ⊤
  ; fromNeg    = λ n → fromℤ (- (+ n))
  }
