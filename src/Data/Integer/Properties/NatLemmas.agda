------------------------------------------------------------------------
-- The Agda standard library
--
-- Some extra lemmas about natural numbers only needed for
-- Data.Integer.Properties (for distributivity)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.Properties.NatLemmas where

open import Data.Nat.Base using (ℕ; _+_; _*_; suc)
open import Data.Nat.Properties
  using (*-distribʳ-+; *-assoc; +-assoc; +-comm; +-suc)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; sym; module ≡-Reasoning)

open ≡-Reasoning

inner-assoc : ∀ m n o → o + (n + m * suc n) * suc o
                ≡ o + n * suc o + m * suc (o + n * suc o)
inner-assoc m n o = begin
  o + (n + m * suc n) * suc o                ≡⟨ cong (o +_) (begin
    (n + m * suc n) * suc o             ≡⟨ *-distribʳ-+ (suc o) n (m * suc n) ⟩
    n * suc o + m * suc n * suc o       ≡⟨ cong (n * suc o +_) (*-assoc m (suc n) (suc o)) ⟩
    n * suc o + m * suc (o + n * suc o) ∎) ⟩
  o + (n * suc o + m * suc (o + n * suc o))  ≡⟨ +-assoc o _ _ ⟨
  o + n * suc o + m * suc (o + n * suc o)    ∎

private
  assoc-comm : ∀ a b c d → a + b + c + d ≡ (a + c) + (b + d)
  assoc-comm a b c d = begin
    a + b + c + d     ≡⟨ cong (_+ d) (+-assoc a b c) ⟩
    a + (b + c) + d   ≡⟨ cong (λ z → a + z + d) (+-comm b c) ⟩
    a + (c + b) + d   ≡⟨ cong (_+ d) (+-assoc a c b) ⟨
    (a + c) + b + d   ≡⟨ +-assoc (a + c) b d ⟩
    (a + c) + (b + d) ∎

  assoc-comm′ : ∀ a b c d → a + (b + (c + d)) ≡ a + c + (b + d)
  assoc-comm′ a b c d = begin
    a + (b + (c + d)) ≡⟨ cong (a +_) (+-assoc b c d) ⟨
    a + (b + c + d)   ≡⟨ cong (λ z → a + (z + d)) (+-comm b c) ⟩
    a + (c + b + d)   ≡⟨ cong (a +_) (+-assoc c b d) ⟩
    a + (c + (b + d)) ≡⟨ +-assoc a c _ ⟨
    a + c + (b + d)   ∎

assoc₁ : ∀ m n o → (2 + n + o) * (1 + m) ≡ (1 + n) * (1 + m) + (1 + o) * (1 + m)
assoc₁ m n o = begin
  (2 + n + o) * (1 + m)                  ≡⟨ cong (_* (1 + m)) (assoc-comm 1 1 n o) ⟩
  ((1 + n) + (1 + o)) * (1 + m)          ≡⟨ *-distribʳ-+ (1 + m) (1 + n) (1 + o) ⟩
  (1 + n) * (1 + m) + (1 + o) * (1 + m)   ∎

assoc₂ : ∀ m n o → (1 + n + (1 + o)) * (1 + m) ≡ (1 + n) * (1 + m) + (1 + o) * (1 + m)
assoc₂ m n o = *-distribʳ-+ (1 + m) (1 + n) (1 + o)

assoc₃ : ∀ m n o → m + (n + (1 + o)) * (1 + m) ≡ (1 + n) * (1 + m) + (m + o * (1 + m))
assoc₃ m n o = begin
  m + (n + (1 + o)) * (1 + m)           ≡⟨ cong (m +_) (*-distribʳ-+ (1 + m) n (1 + o)) ⟩
  m + (n * (1 + m) + (1 + o) * (1 + m)) ≡⟨ +-assoc m _ _ ⟨
  (m + n * (1 + m)) + (1 + o) * (1 + m) ≡⟨ +-suc _ _ ⟩
  (1 + n) * (1 + m) + (m + o * (1 + m)) ∎

assoc₄ : ∀ m n o → m + (1 + m + (n + o) * (1 + m)) ≡ (1 + n) * (1 + m) + (m + o * (1 + m))
assoc₄ m n o = begin
  m + (1 + m + (n + o) * (1 + m))           ≡⟨ +-suc _ _ ⟩
  1 + m + (m + (n + o) * (1 + m))           ≡⟨ cong (λ z → suc (m + (m + z))) (*-distribʳ-+ (suc m) n o) ⟩
  1 + m + (m + (n * (1 + m) + o * (1 + m))) ≡⟨ cong suc (assoc-comm′ m m _ _) ⟩
  (1 + n) * (1 + m) + (m + o * (1 + m))     ∎
