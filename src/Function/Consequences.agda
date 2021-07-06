------------------------------------------------------------------------
-- The Agda standard library
--
-- Relationships between properties of functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Consequences where

import Function.Definitions as FunctionDefinitions
import Function.Structures as FunctionStructures
open import Relation.Binary
open import Level
open import Data.Product
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

private
  variable
    a b ℓ₁ ℓ₂ : Level

module _ (From : Setoid a ℓ₁) (To : Setoid b ℓ₂) where

  open Setoid From using () renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid To   using () renaming (Carrier to B; _≈_ to _≈₂_)
  open FunctionDefinitions _≈₁_ _≈₂_

  inverseᵇ⇒injective : ∀ {f f⁻¹} → FunctionDefinitions.Congruent _≈₂_ _≈₁_ f⁻¹ → Inverseᵇ f f⁻¹ → Injective f
  inverseᵇ⇒injective {f} {f⁻¹} cong₂ (invˡ , invʳ) {x} {y} x≈y = begin
    x         ≈˘⟨ invʳ x ⟩
    f⁻¹ (f x) ≈⟨ cong₂ x≈y ⟩
    f⁻¹ (f y) ≈⟨ invʳ y ⟩
    y         ∎
    where open SetoidReasoning From

  inverseᵇ⇒surjective : ∀ {f f⁻¹} → Inverseᵇ f f⁻¹ → Surjective f
  inverseᵇ⇒surjective {f} {f⁻¹} (invˡ , invʳ) y = (f⁻¹ y , invˡ y)

  inverseᵇ⇒bijective : ∀ {f f⁻¹} → FunctionDefinitions.Congruent _≈₂_ _≈₁_ f⁻¹ → Inverseᵇ f f⁻¹ → Bijective f
  inverseᵇ⇒bijective {f} {f⁻¹} cong₂ inv = (inverseᵇ⇒injective cong₂ inv , inverseᵇ⇒surjective inv)
