------------------------------------------------------------------------
-- The Agda standard library
--
-- Bisimilarity for Conats
------------------------------------------------------------------------

module Codata.Conat.Bisimilarity where

open import Size
open import Codata.Thunk
open import Codata.Conat
open import Relation.Binary

data _≈_ {i} : (m n : Conat i) → Set where
  zero : zero ≈ zero
  suc  : ∀ {m n} → Thunk^R (λ i → _≈_ {i}) i m n → suc m ≈ suc n

refl : ∀ {i} {m : Conat i} → m ≈ m
refl {m = zero}  = zero
refl {m = suc m} = suc λ where .force → refl

sym : ∀ {i} {m n : Conat i} → m ≈ n → n ≈ m
sym zero     = zero
sym (suc eq) = suc λ where .force → sym (eq .force)

trans : ∀ {i} {m n p : Conat i} → m ≈ n → n ≈ p → m ≈ p
trans zero      zero      = zero
trans (suc eq₁) (suc eq₂) = suc λ where .force → trans (eq₁ .force) (eq₂ .force)

data _≤_ {i} : (m n : Conat i) → Set where
  z≤n : ∀ {n : Conat i} → zero ≤ n
  s≤s : ∀ {m n} → Thunk^R (λ i → _≤_ {i}) i m n → suc m ≤ suc n

≤-refl : ∀ {i} {m : Conat i} → m ≤ m
≤-refl {m = zero}  = z≤n
≤-refl {m = suc m} = s≤s λ where .force → ≤-refl

≤-antisym : ∀ {i} {m n : Conat i} → m ≤ n → n ≤ m → m ≈ n
≤-antisym z≤n      z≤n      = zero
≤-antisym (s≤s le) (s≤s ge) = suc λ where .force → ≤-antisym (le .force) (ge .force)

≤-trans : ∀ {i} {m n p : Conat i} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s le₁) (s≤s le₂) = s≤s λ where .force → ≤-trans (le₁ .force) (le₂ .force)
