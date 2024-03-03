------------------------------------------------------------------------
-- The Agda standard library
--
-- Core algebraic definitions
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra`.

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Core where

open import Level using (_⊔_)

------------------------------------------------------------------------
-- Unary and binary operations

Op₁ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₁ A = A → A

Op₂ : ∀ {ℓ} → Set ℓ → Set ℓ
Op₂ A = A → A → A
