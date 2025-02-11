------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for types of functions.
------------------------------------------------------------------------

-- The contents of this file should usually be accessed from `Function`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)

module Function.Definitions.Strict {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

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

StrictlySurjective : (B → A) → Set _
StrictlySurjective f = ∀ y → ∃ λ x → f x ≈ y

StrictlyInverseˡ : (B → A) → (A → B) → Set _
StrictlyInverseˡ f g = ∀ y → f (g y) ≈ y

StrictlyInverseʳ : (A → B) → (B → A) → Set _
StrictlyInverseʳ g f = StrictlyInverseˡ f g

