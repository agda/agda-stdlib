------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for domain theory
------------------------------------------------------------------------




{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Domain.Definitions where

open import Data.Product using (∃-syntax; _×_; _,_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)

private
  variable
    a b ℓ : Level
    A B : Set a

------------------------------------------------------------------------
-- Directed families
------------------------------------------------------------------------

-- IsSemidirectedFamily : (P : Poset c ℓ₁ ℓ₂) → ∀ {Ix : Set c} → (s : Ix → Poset.Carrier P) → Set _
-- IsSemidirectedFamily P {Ix} s = ∀ i j → ∃[ k ] (Poset._≤_ P (s i) (s k) × Poset._≤_ P (s j) (s k))

semidirected : {A : Set a} → Rel A ℓ → (B : Set b) → (B → A) → Set _
semidirected _≤_ B f = ∀ i j → ∃[ k ] (f i ≤ f k × f j ≤ f k)

------------------------------------------------------------------------
-- Least upper bounds
------------------------------------------------------------------------

leastupperbound  : {A : Set a} → Rel A ℓ → (B : Set b) → (B → A) → A → Set _
leastupperbound _≤_ B f lub = (∀ i → f i ≤ lub) × (∀ y → (∀ i → f i ≤ y) → lub ≤ y)
