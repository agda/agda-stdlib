------------------------------------------------------------------------
-- The Agda standard library
--
-- Containers core
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Core where

open import Level
open import Data.Product
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (_↔_; module Inverse)
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

-- Container morphisms

record _⇒_ {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂)
           : Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂) where
  constructor _▷_
  field
    shape    : Shape C₁ → Shape C₂
    position : ∀ {s} → Position C₂ (shape s) → Position C₁ s

  ⟪_⟫ : ∀ {x} {X : Set x} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X
  ⟪_⟫ = map shape (_∘′ position)

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
    ; position = _⟨$⟩_ (Inverse.to position⊸)
    }

  ⟪_⟫⊸ : ∀ {x} {X : Set x} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X
  ⟪_⟫⊸ = ⟪ morphism ⟫

open _⊸_ public using (shape⊸; position⊸; ⟪_⟫⊸)
