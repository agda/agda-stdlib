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
  using (Op₁; Op₂)

------------------------------------------------------------------------
-- Morphism definition in Function.Core

open import Function.Core public
  using (Morphism)

------------------------------------------------------------------------
-- Basic definitions

Homomorphic₀ : (A → B) → A → B → Set _
Homomorphic₀ ⟦_⟧ ∙ ∘ = ⟦ ∙ ⟧ ≈ ∘

Homomorphic₁ : (A → B) → Op₁ A → Op₁ B → Set _
Homomorphic₁ ⟦_⟧ ∙_ ∘_ = ∀ x → ⟦ ∙ x ⟧ ≈ (∘ ⟦ x ⟧)

Homomorphic₂ : (A → B) → Op₂ A → Op₂ B → Set _
Homomorphic₂ ⟦_⟧ _∙_ _∘_ = ∀ x y → ⟦ x ∙ y ⟧ ≈ (⟦ x ⟧ ∘ ⟦ y ⟧)
