------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions that only require an equality
-- relation over the co-domain.
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Function.Definitions.Core2
  {b ℓ₂} {B : Set b} (_≈₂_ : Rel B ℓ₂)
  where

open import Data.Product using (∃)
open import Level using (Level; _⊔_)

------------------------------------------------------------------------
-- Definitions

Surjective : ∀ {a} {A : Set a} → (A → B) → Set (a ⊔ b ⊔ ℓ₂)
Surjective f = ∀ y → ∃ λ x → f x ≈₂ y

-- (Note the name `LeftInverse` is used for the package)
Inverseˡ : ∀ {a} {A : Set a} → (A → B) → (B → A) → Set (b ⊔ ℓ₂)
Inverseˡ f g = ∀ x → f (g x) ≈₂ x
