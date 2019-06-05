------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions that only require an equality
-- relation over the domain.
------------------------------------------------------------------------

-- These definitions should usually be accessed from `Function`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Function.Definitions.Core1
  {a ℓ₁} {A : Set a} (_≈₁_ : Rel A ℓ₁)
  where

open import Level using (_⊔_)

------------------------------------------------------------------------
-- Definitions

-- (Note the name `RightInverse` is used for the package)
Inverseʳ : ∀ {b} {B : Set b} → (A → B) → (B → A) → Set (a ⊔ ℓ₁)
Inverseʳ f g = ∀ x → g (f x) ≈₁ x
