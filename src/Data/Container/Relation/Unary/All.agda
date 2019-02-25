------------------------------------------------------------------------
-- The Agda standard library
--
-- All (□) for containers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Relation.Unary.All where

open import Level using (_⊔_)
open import Relation.Unary using (Pred; _⊆_)
open import Data.Product as Prod using (_,_; proj₁; proj₂; ∃)
open import Function as F

open import Data.Container.Core
import Data.Container.Morphism as M

record □ {s p} (C : Container s p) {x ℓ} {X : Set x}
         (P : Pred X ℓ) (cx : ⟦ C ⟧ X) : Set (p ⊔ ℓ) where
  constructor all
  field proof : ∀ p → P (proj₂ cx p)

module _ {s₁ p₁ s₂ p₂} {C : Container s₁ p₁} {D : Container s₂ p₂}
         {x ℓ ℓ′} {X : Set x} {P : Pred X ℓ} {Q : Pred X ℓ′}
         where

  map : (f : C ⇒ D) → P ⊆ Q → □ C P ⊆ □ D Q ∘′ ⟪ f ⟫
  map f P⊆Q (all prf) .□.proof p = P⊆Q (prf (f .position p))

module _ {s₁ p₁ s₂ p₂} {C : Container s₁ p₁} {D : Container s₂ p₂}
         {x ℓ} {X : Set x} {P : Pred X ℓ}
         where

  map₁ : (f : C ⇒ D) → □ C P ⊆ □ D P ∘′ ⟪ f ⟫
  map₁ f = map f id

module _ {s p} {C : Container s p}
         {x ℓ ℓ′} {X : Set x} {P : Pred X ℓ} {Q : Pred X ℓ′}
         where

  map₂ : P ⊆ Q → □ C P ⊆ □ C Q
  map₂ = map (M.id C)
