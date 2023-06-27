------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions that only require an equality
-- relation over the domain.
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)

module Function.Definitions.Core1
  {a b ℓ₁} {A : Set a} {B : Set b} (_≈₁_ : Rel A ℓ₁)
  where

open import Level using (_⊔_)

------------------------------------------------------------------------
-- Definitions

-- (Note the name `RightInverse` is used for the bundle)
Inverseʳ : (A → B) → (B → A) → Set (a ⊔ ℓ₁)
Inverseʳ f g = ∀ x → g (f x) ≈₁ x
