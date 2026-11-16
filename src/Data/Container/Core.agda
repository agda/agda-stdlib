------------------------------------------------------------------------
-- The Agda standard library
--
-- Containers core
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Core where

open import Level using (Level; _⊔_; suc)
open import Data.Product.Base as Product using (Σ-syntax)
open import Function.Base using (_∘_; _∘′_)
open import Function.Bundles using (Inverse; _↔_)
open import Relation.Unary using (Pred; _⊆_)

-- Definition of Containers

infix 5 _▷_
record Container (s p : Level) : Set (suc (s ⊔ p)) where
  constructor _▷_
  field
    Shape    : Set s
    Position : Shape → Set p
open Container public

-- The semantics ("extension") of a container.

⟦_⟧ : ∀ {s p ℓ} → Container s p → Set ℓ → Set (s ⊔ p ⊔ ℓ)
⟦ S ▷ P ⟧ X = Σ[ s ∈ S ] (P s → X)

-- The extension is a functor

map : ∀ {s p x y} {C : Container s p} {X : Set x} {Y : Set y} →
      (X → Y) → ⟦ C ⟧ X → ⟦ C ⟧ Y
map f = Product.map₂ (f ∘_)

-- Representation of container morphisms.

infixr 8 _⇒_ _⊸_

record _⇒_ {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂)
           : Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂) where
  constructor _▷_
  field
    shape    : Shape C₁ → Shape C₂
    position : ∀ {s} → Position C₂ (shape s) → Position C₁ s

  ⟪_⟫ : ∀ {x} {X : Set x} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X
  ⟪_⟫ = Product.map shape (_∘′ position)

open _⇒_ public

-- Linear container morphisms

record _⊸_ {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂)
  : Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂) where
  field
    shape⊸    : Shape C₁ → Shape C₂
    position⊸ : ∀ {s} → Position C₂ (shape⊸ s) ↔ Position C₁ s

  morphism : C₁ ⇒ C₂
  morphism = record
    { shape    = shape⊸
    ; position = Inverse.to position⊸
    }

  ⟪_⟫⊸ : ∀ {x} {X : Set x} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X
  ⟪_⟫⊸ = ⟪ morphism ⟫

open _⊸_ public using (shape⊸; position⊸; ⟪_⟫⊸)
