------------------------------------------------------------------------
-- The Agda standard library
--
-- Core algebraic definitions
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`.

{-# OPTIONS --without-K --safe #-}

module Algebra.Core where

open import Level using (_⊔_)

------------------------------------------------------------------------
-- Unary and binary operations

Op₁ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₁ A = A → A

Op₂ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₂ A = A → A → A

------------------------------------------------------------------------
-- Left and right actions

Opₗ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Opₗ A B = A → B → B

Opᵣ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Opᵣ A B = B → A → B
