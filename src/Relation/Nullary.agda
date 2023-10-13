------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary where

open import Agda.Builtin.Equality

------------------------------------------------------------------------
-- Re-exports

open import Relation.Nullary.Negation.Core public using
  ( ¬_; _¬-⊎_
  ; contradiction; contradiction₂; contraposition
  )

open import Relation.Nullary.Reflects public using
  ( Reflects; ofʸ; ofⁿ; reflects; reflects′; of; invert; Recomputable
  ; _×-reflects_; _⊎-reflects_; _→-reflects_
  )

open import Relation.Nullary.Decidable.Core public using
  ( Dec; _because_; does; proof; yes′; no′; yes; no; recompute
  ; ¬?; _×-dec_; _⊎-dec_; _→-dec_
  )

------------------------------------------------------------------------
-- Irrelevant types

Irrelevant : ∀ {p} → Set p → Set p
Irrelevant P = ∀ (p₁ p₂ : P) → p₁ ≡ p₂
