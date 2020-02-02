------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for morphisms between algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Algebra.Morphism.Definitions
  {a} (A : Set a)     -- The domain of the morphism
  {b} (B : Set b)     -- The codomain of the morphism
  {ℓ} (_≈_ : Rel B ℓ)  -- The equality relation over the codomain
  where

open import Algebra.Core
open import Function.Core

------------------------------------------------------------------------
-- Basic definitions

Homomorphic₀ : (A → B) → A → B → Set _
Homomorphic₀ ⟦_⟧ ∙ ∘ = ⟦ ∙ ⟧ ≈ ∘

Homomorphic₁ : (A → B) → Op₁ A → Op₁ B → Set _
Homomorphic₁ ⟦_⟧ ∙_ ∘_ = ∀ x → ⟦ ∙ x ⟧ ≈ (∘ ⟦ x ⟧)

Homomorphic₂ : (A → B) → Op₂ A → Op₂ B → Set _
Homomorphic₂ ⟦_⟧ _∙_ _∘_ = ∀ x y → ⟦ x ∙ y ⟧ ≈ (⟦ x ⟧ ∘ ⟦ y ⟧)



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.3

Morphism : Set _
Morphism = A → B

{-# WARNING_ON_USAGE Morphism
"Warning: Morphism was deprecated in v1.3.
Please use the standard function notation (e.g. A → B) instead."
#-}
