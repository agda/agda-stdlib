------------------------------------------------------------------------
-- The Agda standard library
--
-- Core algebraic definitions for module-like structures
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Module`

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Module.Core where

open import Level using (_⊔_)

------------------------------------------------------------------------
-- Left and right actions

Opₗ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Opₗ A B = A → B → B

Opᵣ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
Opᵣ A B = B → A → B
