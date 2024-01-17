------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe public
  using (nothing; just)
  renaming (Maybe to WeaklyDecidable)

------------------------------------------------------------------------
-- Re-exports

open import Relation.Nullary.Negation.Core public
open import Relation.Nullary.Reflects public
open import Relation.Nullary.Decidable.Core public

------------------------------------------------------------------------
-- Irrelevant types

Irrelevant : ∀ {p} → Set p → Set p
Irrelevant P = ∀ (p₁ p₂ : P) → p₁ ≡ p₂

------------------------------------------------------------------------
-- Recomputability - we can rebuild a relevant proof given an
-- irrelevant one.

Recomputable : ∀ {p} → Set p → Set p
Recomputable P = .P → P

