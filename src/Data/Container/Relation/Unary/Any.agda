------------------------------------------------------------------------
-- The Agda standard library
--
-- Any (◇) for containers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Relation.Unary.Any where

open import Level using (_⊔_)
open import Relation.Unary using (Pred; _⊆_)
open import Data.Product as Prod using (_,_; proj₂; ∃)
open import Function

open import Data.Container.Core hiding (map)
import Data.Container.Morphism as M

record ◇ {s p} (C : Container s p) {x ℓ} {X : Set x}
         (P : Pred X ℓ) (cx : ⟦ C ⟧ X) : Set (p ⊔ ℓ) where
  constructor any
  field proof : ∃ λ p → P (proj₂ cx p)

module _ {s₁ p₁ s₂ p₂} {C : Container s₁ p₁} {D : Container s₂ p₂}
         {x ℓ ℓ′} {X : Set x} {P : Pred X ℓ} {Q : Pred X ℓ′}
         where

  map : (f : C ⇒ D) → P ⊆ Q → ◇ D P ∘′ ⟪ f ⟫ ⊆ ◇ C Q
  map f P⊆Q (any (p , P)) .◇.proof = f .position p , P⊆Q P


module _ {s₁ p₁ s₂ p₂} {C : Container s₁ p₁} {D : Container s₂ p₂}
         {x ℓ} {X : Set x} {P : Pred X ℓ}
         where

  map₁ : (f : C ⇒ D) → ◇ D P ∘′ ⟪ f ⟫ ⊆ ◇ C P
  map₁ f = map f id


module _ {s p} {C : Container s p}
         {x ℓ ℓ′} {X : Set x} {P : Pred X ℓ} {Q : Pred X ℓ′}
         where

  map₂ : P ⊆ Q → ◇ C P ⊆ ◇ C Q
  map₂ = map (M.id C)
