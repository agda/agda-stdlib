------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definitions for morphisms between algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Relation.Binary.Morphism.Definitions
  {a} (A : Set a)     -- The domain of the morphism
  {b} (B : Set b)     -- The codomain of the morphism
  where

open import Level using (Level)

private
  variable
    ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Morphism definition in Function.Core

open import Function.Core public
  using (Morphism)

------------------------------------------------------------------------
-- Basic definitions

Homomorphic₂ : Rel A ℓ₁ → Rel B ℓ₂ → (A → B) → Set _
Homomorphic₂ _∼₁_ _∼₂_ ⟦_⟧ = ∀ {x y} → x ∼₁ y → ⟦ x ⟧ ∼₂ ⟦ y ⟧
