------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties connecting left-scaling and right-scaling over the same scalars
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary

module Algebra.Module.Definitions.Bi.Simultaneous
  {a b ℓb} (A : Set a) {B : Set b} (_≈_ : Rel B ℓb)
  where

open import Algebra.Module.Core

Coincident : Opₗ A B → Opᵣ A B → Set _
Coincident _∙ₗ_ _∙ᵣ_ = ∀ x m → (x ∙ₗ m) ≈ (m ∙ᵣ x)
