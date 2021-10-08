------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for morphisms between module-like algebraic
-- structures
------------------------------------------------------------------------
{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Algebra.Module.Morphism.Definitions
  {r} (R : Set r) -- The underlying ring
  {a} (A : Set a) -- The domain of the morphism
  {b} (B : Set b) -- The codomain of the morphism
  {ℓ} (_≈_ : Rel B ℓ) -- The equality relation over the codomain
  where

open import Algebra.Core
open import Algebra.Morphism.Definitions A B _≈_ public

Homomorphicₗ : (A → B) → Opₗ R A → Opₗ R B → Set _
Homomorphicₗ ⟦_⟧ _∙_ _∘_ = ∀ r x → ⟦ r ∙ x ⟧ ≈ (r ∘ ⟦ x ⟧)
