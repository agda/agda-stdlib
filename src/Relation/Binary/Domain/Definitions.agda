------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions for domain theory
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Domain.Definitions where

open import Data.Product using (∃-syntax; _×_; _,_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Morphism.Structures using (IsOrderHomomorphism)

private
  variable
    c o ℓ e o' ℓ' e' ℓ₁ ℓ₂ : Level
    Ix A B : Set o
    P : Poset c ℓ e

------------------------------------------------------------------------
-- Directed families
------------------------------------------------------------------------

IsSemidirectedFamily : (P : Poset c ℓ₁ ℓ₂) → ∀ {Ix : Set c} → (s : Ix → Poset.Carrier P) → Set _
IsSemidirectedFamily P {Ix} s = ∀ i j → ∃[ k ] (Poset._≤_ P (s i) (s k) × Poset._≤_ P (s j) (s k))

