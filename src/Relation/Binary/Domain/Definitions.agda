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
-- Upper bound
------------------------------------------------------------------------

UpperBound : {A : Set a} → Rel A ℓ → {B : Set b} → (f : B → A) → A → Set _
UpperBound _≤_ f x = ∀ i → f i ≤ x
