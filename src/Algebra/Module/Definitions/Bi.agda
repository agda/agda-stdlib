------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties connecting left-scaling and right-scaling
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

-- The properties are parameterised by the three carriers and
-- the result equality.

module Algebra.Module.Definitions.Bi
  {a a′ b ℓb} (A : Set a) (A′ : Set a′) {B : Set b} (_≈_ : Rel B ℓb)
  where

  open import Algebra.Core

  Associative : Opₗ A B → Opᵣ A′ B → Set _
  Associative _∙ₗ_ _∙ᵣ_ = ∀ x m y → ((x ∙ₗ m) ∙ᵣ y) ≈ (x ∙ₗ (m ∙ᵣ y))
