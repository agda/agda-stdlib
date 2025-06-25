------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for domain theory
------------------------------------------------------------------------




{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Domain.Definitions where

open import Data.Product using (∃-syntax; _×_; _,_)
open import Function using (_∘_)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Core using (Rel)

private
  variable
    a b i ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b
    I : Set ℓ

------------------------------------------------------------------------
-- Directed families
------------------------------------------------------------------------

semidirected : {A : Set a} → Rel A ℓ → (B : Set b) → (B → A) → Set _
semidirected _≤_ B f = ∀ i j → ∃[ k ] (f i ≤ f k × f j ≤ f k)

------------------------------------------------------------------------
-- Least upper bounds
------------------------------------------------------------------------

leastupperbound  : {A : Set a} → Rel A ℓ → {B : Set b} → (g : B → A) → A → Set _
leastupperbound _≤_ g lub = (∀ i → g i ≤ lub) × (∀ y → (∀ i → g i ≤ y) → lub ≤ y)

preserveLubs : {A : Set a} {B : Set b } (≤₁ : Rel A ℓ₁) (≤₂ : Rel B ℓ₂) (f : A → B) → Set (suc (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂))
preserveLubs ≤₁ ≤₂ f =  ∀ I → ∀ {g : I → _} → ∀ lub → leastupperbound ≤₁ g lub → leastupperbound ≤₂ (f ∘ g) (f lub)
