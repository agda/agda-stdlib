------------------------------------------------------------------------
-- The Agda standard library
--
-- Division with remainder for integers constructed as a pair of naturals
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Integer.IntConstruction.DivMod where

open import Data.Fin.Base as Fin using (Fin)
import Data.Fin.Properties as Fin
open import Data.Integer.IntConstruction
open import Data.Integer.IntConstruction.Properties
open import Data.Nat.Base as ℕ using (ℕ)
import Data.Nat.Properties as ℕ
import Data.Nat.DivMod as ℕ
open import Function.Base
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

-- should the divisor also be an integer?
record DivMod (dividend : ℤ) (divisor : ℕ) : Set where
  field
    quotient : ℤ
    remainder : ℕ
    remainder<divisor : remainder ℕ.< divisor
    property : dividend ≃ ⁺ remainder + quotient * ⁺ divisor

divMod : ∀ i n .{{_ : ℕ.NonZero n}} → DivMod i n
divMod (a ⊖ b) n = record
  { quotient = quotient
  ; remainder<divisor = remainder<n
  ; property = property
  }
  where
    open ≡-Reasoning

  -- either the actual quotient or one above it
    quotient′ : ℤ
    quotient′ = (a ℕ./ n) ⊖ (b ℕ./ n)

    remainder′ : ℤ
    remainder′ = (a ℕ.% n) ⊖ (b ℕ.% n)

    property′ : a ⊖ b ≃ remainder′ + quotient′ * ⁺ n
    property′ = mk≃ $ cong₂ ℕ._+_ left right
      where
        left : a ≡ a ℕ.% n ℕ.+ (a ℕ./ n ℕ.* n ℕ.+ b ℕ./ n ℕ.* 0)
        left = begin
          a                                             ≡⟨ ℕ.m≡m%n+[m/n]*n a n ⟩
          a ℕ.% n ℕ.+ a ℕ./ n ℕ.* n                     ≡⟨ cong (a ℕ.% n ℕ.+_) (ℕ.+-identityʳ (a ℕ./ n ℕ.* n)) ⟨
          a ℕ.% n ℕ.+ (a ℕ./ n ℕ.* n ℕ.+ 0)             ≡⟨ cong (λ z → a ℕ.% n ℕ.+ (a ℕ./ n ℕ.* n ℕ.+ z)) (ℕ.*-zeroʳ (b ℕ./ n)) ⟨
          a ℕ.% n ℕ.+ (a ℕ./ n ℕ.* n ℕ.+ b ℕ./ n ℕ.* 0) ∎

        right : b ℕ.% n ℕ.+ (a ℕ./ n ℕ.* 0 ℕ.+ b ℕ./ n ℕ.* n) ≡ b
        right = begin
          b ℕ.% n ℕ.+ (a ℕ./ n ℕ.* 0 ℕ.+ b ℕ./ n ℕ.* n) ≡⟨ cong (λ z → b ℕ.% n ℕ.+ (z ℕ.+ b ℕ./ n ℕ.* n)) (ℕ.*-zeroʳ (a ℕ./ n)) ⟩
          b ℕ.% n ℕ.+ (0 ℕ.+ b ℕ./ n ℕ.* n)             ≡⟨ cong (b ℕ.% n ℕ.+_) (ℕ.+-identityˡ (b ℕ./ n ℕ.* n)) ⟩
          b ℕ.% n ℕ.+ b ℕ./ n ℕ.* n                     ≡⟨ ℕ.m≡m%n+[m/n]*n b n ⟨
          b                                             ∎

    quotient : ℤ
    quotient with b ℕ.% n ℕ.≤? a ℕ.% n
    ... | yes _ = quotient′
    ... | no _ = pred quotient′

    remainder : ℕ
    remainder with b ℕ.% n ℕ.≤? a ℕ.% n
    ... | yes _ = a ℕ.% n ℕ.∸ b ℕ.% n
    ... | no _ = n ℕ.∸ (b ℕ.% n ℕ.∸ a ℕ.% n)

    remainder<n : remainder ℕ.< n
    remainder<n with b ℕ.% n ℕ.≤? a ℕ.% n
    ... | yes _ = ℕ.≤-<-trans (ℕ.m∸n≤m (a ℕ.% n) (b ℕ.% n)) (ℕ.m%n<n a n)
    ... | no b%n≰a%n = ℕ.∸-monoʳ-< {o = 0} (ℕ.m<n⇒0<n∸m (ℕ.≰⇒> b%n≰a%n)) (ℕ.≤-trans (ℕ.m∸n≤m (b ℕ.% n) (a ℕ.% n)) (ℕ.<⇒≤ (ℕ.m%n<n b n)))

    property : a ⊖ b ≃ ⁺ remainder + quotient * ⁺ n
    property with b ℕ.% n ℕ.≤? a ℕ.% n
    ... | yes p = ≃-trans property′ (+-cong rem-prop ≃-refl)
      where
        rem-prop : remainder′ ≃ ⁺ (a ℕ.% n ℕ.∸ b ℕ.% n)
        rem-prop = mk≃ $ begin
          a ℕ.% n ℕ.+ 0                   ≡⟨ ℕ.+-identityʳ (a ℕ.% n) ⟩
          a ℕ.% n                         ≡⟨ ℕ.m∸n+n≡m p ⟨
          a ℕ.% n ℕ.∸ b ℕ.% n ℕ.+ b ℕ.% n ∎
    ... | no b%n≰a%n = ≃-trans property′ $ mk≃ $ begin
      (w ℕ.+ x) ℕ.+ (y ℕ.+ (n ℕ.+ z))                 ≡⟨ cong ((w ℕ.+ x) ℕ.+_) (ℕ.+-assoc y n z) ⟨
      (w ℕ.+ x) ℕ.+ ((y ℕ.+ n) ℕ.+ z)                 ≡⟨ cong (λ k → (w ℕ.+ x) ℕ.+ (k ℕ.+ z)) (ℕ.+-comm y n) ⟩
      (w ℕ.+ x) ℕ.+ ((n ℕ.+ y) ℕ.+ z)                 ≡⟨ cong ((w ℕ.+ x) ℕ.+_) (ℕ.+-assoc n y z) ⟩
      (w ℕ.+ x) ℕ.+ (n ℕ.+ (y ℕ.+ z))                 ≡⟨ ℕ.+-assoc (w ℕ.+ x) n (y ℕ.+ z) ⟨
      ((w ℕ.+ x) ℕ.+ n) ℕ.+ (y ℕ.+ z)                 ≡⟨ cong (ℕ._+ (y ℕ.+ z)) (ℕ.+-comm (w ℕ.+ x) n) ⟩
      (n ℕ.+ (w ℕ.+ x)) ℕ.+ (y ℕ.+ z)                 ≡⟨ cong (ℕ._+ (y ℕ.+ z)) (ℕ.+-assoc n w x) ⟨
      ((n ℕ.+ w) ℕ.+ x) ℕ.+ (y ℕ.+ z)                 ≡⟨ cong (λ k → ((n ℕ.+ k) ℕ.+ x) ℕ.+ (y ℕ.+ z)) (ℕ.m∸[m∸n]≡n (ℕ.≰⇒≥ b%n≰a%n)) ⟨
      ((n ℕ.+ (v ℕ.∸ (v ℕ.∸ w))) ℕ.+ x) ℕ.+ (y ℕ.+ z) ≡⟨ cong (λ k → (k ℕ.+ x) ℕ.+ (y ℕ.+ z)) (ℕ.+-∸-assoc n (ℕ.m∸n≤m v w)) ⟨
      (((n ℕ.+ v) ℕ.∸ (v ℕ.∸ w)) ℕ.+ x) ℕ.+ (y ℕ.+ z) ≡⟨ cong (λ k → (k ℕ.+ x) ℕ.+ (y ℕ.+ z)) (ℕ.+-∸-comm v (ℕ.≤-trans (ℕ.m∸n≤m v w) (ℕ.<⇒≤ (ℕ.m%n<n b n)))) ⟩
      (((n ℕ.∸ (v ℕ.∸ w)) ℕ.+ v) ℕ.+ x) ℕ.+ (y ℕ.+ z) ≡⟨ cong (ℕ._+ (y ℕ.+ z)) (ℕ.+-assoc (n ℕ.∸ (v ℕ.∸ w)) v x) ⟩
      ((n ℕ.∸ (v ℕ.∸ w)) ℕ.+ (v ℕ.+ x)) ℕ.+ (y ℕ.+ z) ≡⟨ cong (λ k → ((n ℕ.∸ (v ℕ.∸ w)) ℕ.+ k) ℕ.+ (y ℕ.+ z)) (ℕ.+-comm v x) ⟩
      ((n ℕ.∸ (v ℕ.∸ w)) ℕ.+ (x ℕ.+ v)) ℕ.+ (y ℕ.+ z) ≡⟨ cong (ℕ._+ (y ℕ.+ z)) (ℕ.+-assoc (n ℕ.∸ (v ℕ.∸ w)) x v) ⟨
      (((n ℕ.∸ (v ℕ.∸ w)) ℕ.+ x) ℕ.+ v) ℕ.+ (y ℕ.+ z) ≡⟨ ℕ.+-assoc (n ℕ.∸ (v ℕ.∸ w) ℕ.+ x) v (y ℕ.+ z) ⟩
      ((n ℕ.∸ (v ℕ.∸ w)) ℕ.+ x) ℕ.+ (v ℕ.+ (y ℕ.+ z)) ∎
      where
        w = a ℕ.% n
        x = a ℕ./ n ℕ.* n ℕ.+ b ℕ./ n ℕ.* 0
        y = a ℕ./ n ℕ.* 0
        z = b ℕ./ n ℕ.* n
        v = b ℕ.% n
