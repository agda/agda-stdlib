{-# OPTIONS --safe --cubical-compatible #-}

module Data.Integer.IntConstruction where

open import Data.Nat.Base as ℕ using (ℕ)
open import Function.Base using (flip)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

infixl 6 _⊖_

record ℤ : Set where
  constructor _⊖_
  field
    minuend : ℕ
    subtrahend : ℕ

_≃_ : Rel ℤ _
(a ⊖ b) ≃ (c ⊖ d) = a ℕ.+ d ≡ c ℕ.+ b

_≤_ : Rel ℤ _
(a ⊖ b) ≤ (c ⊖ d) = a ℕ.+ d ℕ.≤ c ℕ.+ b

_≥_ : Rel ℤ _
_≥_ = flip _≤_

_<_ : Rel ℤ _
(a ⊖ b) < (c ⊖ d) = a ℕ.+ d ℕ.< c ℕ.+ b

_>_ : Rel ℤ _
_>_ = flip _<_

0ℤ : ℤ
0ℤ = 0 ⊖ 0

1ℤ : ℤ
1ℤ = 1 ⊖ 0

_+_ : ℤ → ℤ → ℤ
(a ⊖ b) + (c ⊖ d) = (a ℕ.+ c) ⊖ (b ℕ.+ d)

_*_ : ℤ → ℤ → ℤ
(a ⊖ b) * (c ⊖ d) = (a ℕ.* c ℕ.+ b ℕ.* d) ⊖ (a ℕ.* d ℕ.+ b ℕ.* c)

-_ : ℤ → ℤ
- (a ⊖ b) = b ⊖ a

∣_∣ : ℤ → ℕ
∣ a ⊖ b ∣ = ℕ.∣ a - b ∣′

