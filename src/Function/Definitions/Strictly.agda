------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions.
------------------------------------------------------------------------

-- The contents of this module should usually be accessed from `Function`,
-- moreover via qualified import to disambiguate from `Function.Definitions`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)

module Function.Definitions.Strictly {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Data.Product.Base using (∃)
open import Level using (Level)

private
  variable
    b : Level
    B : Set b

------------------------------------------------------------------------
-- Strict definitions

-- These are often easier to use once but much harder to compose and
-- reason about.

Surjective : (B → A) → Set _
Surjective f = ∀ y → ∃ λ x → f x ≈ y

Inverseˡ : (B → A) → (A → B) → Set _
Inverseˡ f g = ∀ y → f (g y) ≈ y

Inverseʳ : (A → B) → (B → A) → Set _
Inverseʳ g f = Inverseˡ f g

