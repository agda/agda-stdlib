------------------------------------------------------------------------
-- The Agda standard library
--
-- Containers core
------------------------------------------------------------------------

module Data.Container.Core where

open import Level
open import Data.Product

infix 5 _▷_
record Container (s p : Level) : Set (suc (s ⊔ p)) where
  constructor _▷_
  field
    Shape    : Set s
    Position : Shape → Set p

-- The semantics ("extension") of a container.

⟦_⟧ : ∀ {s p ℓ} → Container s p → Set ℓ → Set (s ⊔ p ⊔ ℓ)
⟦ S ▷ P ⟧ X = Σ[ s ∈ S ] (P s → X)
