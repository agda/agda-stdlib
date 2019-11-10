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

open import Algebra.Core
open import Function.Base
open import Level using (Level)

private
  variable
    ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Basic definitions

Morphism : Set _
Morphism = A → B

Homomorphic₂ : Rel A ℓ₁ → Rel B ℓ₂ → Morphism → Set _
Homomorphic₂ _∼₁_ _∼₂_ ⟦_⟧ = ∀ {x y} → x ∼₁ y → ⟦ x ⟧ ∼₂ ⟦ y ⟧
