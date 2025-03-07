------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise equality for containers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Container.Relation.Binary.Pointwise where

open import Data.Product.Base using (_,_; Σ-syntax; -,_; proj₁; proj₂)
open import Data.Container.Core using (Container; ⟦_⟧)
open import Function.Base using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary.Core using (REL; _⇒_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; subst)

-- Equality, parametrised on an underlying relation.

module _ {s p} (C : Container s p) where

  record Pointwise {x y e} {X : Set x} {Y : Set y} (R : REL X Y e)
                   (cx : ⟦ C ⟧ X) (cy : ⟦ C ⟧ Y) : Set (s ⊔ p ⊔ e) where
    constructor _,_
    field shape    : proj₁ cx ≡ proj₁ cy
          position : ∀ p → R (proj₂ cx p) (proj₂ cy (subst _ shape p))
  infixr 4 _,_

module _ {s p} {C : Container s p} {x y} {X : Set x} {Y : Set y}
         {ℓ ℓ′} {R : REL X Y ℓ} {R′ : REL X Y ℓ′}
         where

  map : R ⇒ R′ → Pointwise C R ⇒ Pointwise C R′
  map R⇒R′ (s , f) = s , R⇒R′ ∘ f
