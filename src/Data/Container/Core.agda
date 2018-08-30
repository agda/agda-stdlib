------------------------------------------------------------------------
-- The Agda standard library
--
-- Containers core
------------------------------------------------------------------------

module Data.Container.Core where

open import Level
open import Data.Product
open import Function
open import Relation.Unary using (Pred)

-- Definition of Containers

infix 5 _▷_
record Container (s p : Level) : Set (suc (s ⊔ p)) where
  constructor _▷_
  field
    Shape    : Set s
    Position : Shape → Set p
open Container

-- The semantics ("extension") of a container.

⟦_⟧ : ∀ {s p ℓ} → Container s p → Set ℓ → Set (s ⊔ p ⊔ ℓ)
⟦ S ▷ P ⟧ X = Σ[ s ∈ S ] (P s → X)

-- Representation of container morphisms.

record _⇒_ {s₁ s₂ p₁ p₂} (C₁ : Container s₁ p₁) (C₂ : Container s₂ p₂)
           : Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂) where
  constructor _▷_
  field
    shape    : Shape C₁ → Shape C₂
    position : ∀ {s} → Position C₂ (shape s) → Position C₁ s
open _⇒_ public

-- Interpretation of _⇒_.

⟪_⟫ : ∀ {s₁ s₂ p₁ p₂ x} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂} →
      C₁ ⇒ C₂ → {X : Set x} → ⟦ C₁ ⟧ X → ⟦ C₂ ⟧ X
⟪ m ⟫ = map (shape m) (_∘ position m)

-- All and Any

module _ {s p} {C : Container s p} {x} {X : Set x} where

  □ : ∀ {ℓ} → Pred X ℓ → Pred (⟦ C ⟧ X) (p ⊔ ℓ)
  □ P (s , f) = ∀ p → P (f p)

  ◇ : ∀ {ℓ} → Pred X ℓ → Pred (⟦ C ⟧ X) (p ⊔ ℓ)
  ◇ P (s , f) = ∃ λ p → P (f p)
