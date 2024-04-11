------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Literals where

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromNeg using (Negative)
open import Data.Unit.Base using (⊤)
open import Data.Nat.Base using (ℕ; zero)
open import Data.Nat.Coprimality using (sym; 1-coprimeTo)
open import Data.Integer.Base using (ℤ; ∣_∣; +_; -_)
open import Data.Rational.Base using (ℚ)

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
