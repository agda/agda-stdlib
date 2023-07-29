------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions that only require an equality
-- relation over the co-domain.
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)

module Function.Definitions.Core2
  {a b ℓ₂} {A : Set a} {B : Set b} (_≈₂_ : Rel B ℓ₂)
  where

open import Data.Product.Base using (∃)
open import Level using (Level; _⊔_)

------------------------------------------------------------------------
-- Definitions

Surjective : (A → B) → Set (a ⊔ b ⊔ ℓ₂)
Surjective f = ∀ y → ∃ λ x → f x ≈₂ y

-- (Note the name `LeftInverse` is used for the bundle)
Inverseˡ : (A → B) → (B → A) → Set (b ⊔ ℓ₂)
Inverseˡ f g = ∀ x → f (g x) ≈₂ x
