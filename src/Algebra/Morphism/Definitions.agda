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

Morphism : Set _
Morphism = A → B

Homomorphic₀ : Morphism → A → B → Set _
Homomorphic₀ ⟦_⟧ ∙ ∘ = ⟦ ∙ ⟧ ≈ ∘

Homomorphic₁ : Morphism → Fun₁ A → Op₁ B → Set _
Homomorphic₁ ⟦_⟧ ∙_ ∘_ = ∀ x → ⟦ ∙ x ⟧ ≈ (∘ ⟦ x ⟧)

Homomorphic₂ : Morphism → Fun₂ A → Op₂ B → Set _
Homomorphic₂ ⟦_⟧ _∙_ _∘_ = ∀ x y → ⟦ x ∙ y ⟧ ≈ (⟦ x ⟧ ∘ ⟦ y ⟧)
