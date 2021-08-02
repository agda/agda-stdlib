------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of lattice relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Relation.Binary.Lattice`.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Lattice.Definitions where

open import Algebra.Core
open import Data.Product using (_×_; _,_)
open import Function.Base using (flip)
open import Relation.Binary

------------------------------------------------------------------------
-- Relationships between orders and operators

Supremum : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Set _
Supremum _≤_ _∨_ =
  ∀ x y → x ≤ (x ∨ y) × y ≤ (x ∨ y) × ∀ z → x ≤ z → y ≤ z → (x ∨ y) ≤ z

Infimum : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Set _
Infimum _≤_ = Supremum (flip _≤_)

Exponential : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Op₂ A → Op₂ A → Set _
Exponential _≤_ _∧_ _⇨_ =
  ∀ w x y → ((w ∧ x) ≤ y → w ≤ (x ⇨ y)) × (w ≤ (x ⇨ y) → (w ∧ x) ≤ y)
