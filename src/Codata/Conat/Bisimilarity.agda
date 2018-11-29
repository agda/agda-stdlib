------------------------------------------------------------------------
-- The Agda standard library
--
-- Bisimilarity for Conats
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Codata.Conat.Bisimilarity where

open import Size
open import Codata.Thunk
open import Codata.Conat
open import Relation.Binary

infix 1 _⊢_≈_
data _⊢_≈_ i : (m n : Conat ∞) → Set where
  zero : i ⊢ zero ≈ zero
  suc  : ∀ {m n} → Thunk^R _⊢_≈_ i m n → i ⊢ suc m ≈ suc n

refl : ∀ {i m} → i ⊢ m ≈ m
refl {m = zero}  = zero
refl {m = suc m} = suc λ where .force → refl

sym : ∀ {i m n} → i ⊢ m ≈ n → i ⊢ n ≈ m
sym zero     = zero
sym (suc eq) = suc λ where .force → sym (eq .force)

trans : ∀ {i m n p} → i ⊢ m ≈ n → i ⊢ n ≈ p → i ⊢ m ≈ p
trans zero      zero      = zero
trans (suc eq₁) (suc eq₂) = suc λ where .force → trans (eq₁ .force) (eq₂ .force)

infix 1 _⊢_≲_
data _⊢_≲_ i : (m n : Conat ∞) → Set where
  z≲n : ∀ {n} → i ⊢ zero ≲ n
  s≲s : ∀ {m n} → Thunk^R _⊢_≲_ i m n → i ⊢ suc m ≲ suc n

≈⇒≲ : ∀ {i m n} → i ⊢ m ≈ n → i ⊢ m ≲ n
≈⇒≲ zero     = z≲n
≈⇒≲ (suc eq) = s≲s λ where .force → ≈⇒≲ (eq .force)

≲-refl : ∀ {i m} → i ⊢ m ≲ m
≲-refl = ≈⇒≲ refl

≲-antisym : ∀ {i m n} → i ⊢ m ≲ n → i ⊢ n ≲ m → i ⊢ m ≈ n
≲-antisym z≲n      z≲n      = zero
≲-antisym (s≲s le) (s≲s ge) = suc λ where .force → ≲-antisym (le .force) (ge .force)

≲-trans : ∀ {i m n p} → i ⊢ m ≲ n → i ⊢ n ≲ p → i ⊢ m ≲ p
≲-trans z≲n       _         = z≲n
≲-trans (s≲s le₁) (s≲s le₂) = s≲s λ where .force → ≲-trans (le₁ .force) (le₂ .force)
