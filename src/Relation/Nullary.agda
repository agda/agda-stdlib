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

open import Relation.Nullary.Negation.Core public
open import Relation.Nullary.Reflects public
open import Relation.Nullary.Decidable.Core public

------------------------------------------------------------------------
-- Irrelevant types

Irrelevant : ∀ {p} → Set p → Set p
Irrelevant P = ∀ (p₁ p₂ : P) → p₁ ≡ p₂
