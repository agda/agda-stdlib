------------------------------------------------------------------------
-- The Agda standard library
--
-- To be merged into Data.Integer.Properties before merging!
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Integer.IntConstruction.IntProperties where

open import Data.Integer.Base
open import Data.Integer.IntConstruction as INT using (_≃_)
open import Data.Integer.IntConstruction.Tmp
open import Data.Integer.Properties
import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality

fromINT-cong : ∀ {i j} → i ≃ j → fromINT i ≡ fromINT j
fromINT-cong {a INT.⊖ b} {c INT.⊖ d} a+d≡c+b = begin
  a ⊖ b                       ≡⟨ m-n≡m⊖n a b ⟨
  + a - + b                   ≡⟨ cong (_- + b) (+-identityʳ (+ a)) ⟨
  (+ a + 0ℤ) - + b            ≡⟨ cong (λ z → (+ a + z) - + b) (+-inverseʳ (+ d)) ⟨
  (+ a + (+ d - + d)) - + b   ≡⟨ cong (_- + b) (+-assoc (+ a) (+ d) (- + d)) ⟨
  (+ (a ℕ.+ d) - + d) - + b   ≡⟨ cong (λ z → (+ z - + d) - + b) a+d≡c+b ⟩
  (+ (c ℕ.+ b) - + d) - + b   ≡⟨ cong (_- + b) (+-assoc (+ c) (+ b) (- + d)) ⟩
  (+ c + (+ b - + d)) - + b   ≡⟨ cong (λ z → (+ c + z) - + b) (+-comm (+ b) (- + d)) ⟩
  (+ c + (- + d + + b)) - + b ≡⟨ cong (_- + b) (+-assoc (+ c) (- + d) (+ b)) ⟨
  ((+ c - + d) + + b) - + b   ≡⟨ +-assoc (+ c - + d) (+ b) (- + b) ⟩
  (+ c - + d) + (+ b - + b)   ≡⟨ cong₂ _+_ (m-n≡m⊖n c d) (+-inverseʳ (+ b)) ⟩
  c ⊖ d + 0ℤ                  ≡⟨ +-identityʳ (c ⊖ d) ⟩
  c ⊖ d                       ∎
  where open ≡-Reasoning

fromINT-injective : ∀ {i j} → fromINT i ≡ fromINT j → i ≃ j
fromINT-injective {a INT.⊖ b} {c INT.⊖ d} a⊖b≡c⊖d = +-injective $ begin
  + a + + d                   ≡⟨ cong (_+ + d) (+-identityʳ (+ a)) ⟨
  (+ a + 0ℤ) + + d            ≡⟨ cong (λ z → (+ a + z) + + d) (+-inverseˡ (+ b)) ⟨
  (+ a + (- + b + + b)) + + d ≡⟨ cong (_+ + d) (+-assoc (+ a) (- + b) (+ b)) ⟨
  ((+ a - + b) + + b) + + d   ≡⟨ cong (λ z → (z + + b) + + d) (m-n≡m⊖n a b) ⟩
  (a ⊖ b + + b) + + d         ≡⟨ cong (λ z → (z + + b) + + d) a⊖b≡c⊖d ⟩
  (c ⊖ d + + b) + + d         ≡⟨ cong (λ z → (z + + b) + + d) (m-n≡m⊖n c d) ⟨
  ((+ c - + d) + + b) + + d   ≡⟨ cong (_+ + d) (+-assoc (+ c) (- + d) (+ b)) ⟩
  (+ c + (- + d + + b)) + + d ≡⟨ cong (λ z → (+ c + z) + + d) (+-comm (- + d) (+ b)) ⟩
  (+ c + (+ b - + d)) + + d   ≡⟨ cong (_+ + d) (+-assoc (+ c) (+ b) (- + d)) ⟨
  ((+ c + + b) - + d) + + d   ≡⟨ +-assoc (+ c + + b) (- + d) (+ d) ⟩
  (+ c + + b) + (- + d + + d) ≡⟨ cong (_+_ (+ c + + b)) (+-inverseˡ (+ d)) ⟩
  (+ c + + b) + 0ℤ            ≡⟨ +-identityʳ (+ c + + b) ⟩
  + c + + b                   ∎
  where open ≡-Reasoning

fromINT-surjective : ∀ j → ∃[ i ] ∀ {z} → z ≃ i → fromINT z ≡ j
fromINT-surjective j .proj₁ = toINT j
fromINT-surjective (+ n) .proj₂ {a INT.⊖ b} a+0≡n+b = begin
  a ⊖ b             ≡⟨ m-n≡m⊖n a b ⟨
  + a - + b         ≡⟨ cong (_- + b) (+-identityʳ (+ a)) ⟨
  (+ a + 0ℤ) - + b  ≡⟨ cong (λ z → + z - + b) a+0≡n+b ⟩
  (+ n + + b) - + b ≡⟨ +-assoc (+ n) (+ b) (- + b) ⟩
  + n + (+ b - + b) ≡⟨ cong (_+_ (+ n)) (+-inverseʳ (+ b)) ⟩
  + n + 0ℤ          ≡⟨ +-identityʳ (+ n) ⟩
  + n               ∎
  where open ≡-Reasoning
fromINT-surjective (-[1+ n ]) .proj₂ {a INT.⊖ b} a+sn≡b = begin
  a ⊖ b                     ≡⟨ m-n≡m⊖n a b ⟨
  + a - + b                 ≡⟨ cong (λ z → + a - + z) a+sn≡b ⟨
  + a - (+ a + + ℕ.suc n)   ≡⟨ cong (_+_ (+ a)) (neg-distrib-+ (+ a) (+ ℕ.suc n)) ⟩
  + a + (- + a - + ℕ.suc n) ≡⟨ +-assoc (+ a) (- + a) (- + ℕ.suc n) ⟨
  (+ a - + a) - + ℕ.suc n   ≡⟨ cong (_- + ℕ.suc n) (+-inverseʳ (+ a)) ⟩
  0ℤ - + ℕ.suc n            ≡⟨ +-identityˡ (- + ℕ.suc n) ⟩
  -[1+ n ]                  ∎
  where open ≡-Reasoning
