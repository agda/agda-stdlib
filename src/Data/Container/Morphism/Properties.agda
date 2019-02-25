------------------------------------------------------------------------
-- The Agda standard library
--
-- Propertiers of any for containers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Morphism.Properties where

import Function as F
open import Relation.Binary.PropositionalEquality

open import Data.Container.Core
open import Data.Container.Morphism

-- Identity

module _ {s p} (C : Container s p) where

  id-correct : ∀ {x} {X : Set x} → ⟪ id C ⟫ {X = X} ≗ F.id
  id-correct x = refl

-- Composition.

module _ {s₁ s₂ s₃ p₁ p₂ p₃}
         {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂} {C₃ : Container s₃ p₃}
         where

  ∘-correct : (f : C₂ ⇒ C₃) (g : C₁ ⇒ C₂) → ∀ {x} {X : Set x} →
              ⟪ f ∘ g ⟫ {X = X} ≗ (⟪ f ⟫ F.∘ ⟪ g ⟫)
  ∘-correct f g xs = refl
