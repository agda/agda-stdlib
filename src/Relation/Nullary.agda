------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Maybe using (Maybe)
open import Level using (Level)

private
  variable
    p : Level
    P : Set p


------------------------------------------------------------------------
-- Re-exports

open import Relation.Nullary.Negation.Core public
open import Relation.Nullary.Reflects public
open import Relation.Nullary.Decidable.Core public

------------------------------------------------------------------------
-- Irrelevant types

Irrelevant : Set p → Set p
Irrelevant P = ∀ (p₁ p₂ : P) → p₁ ≡ p₂

------------------------------------------------------------------------
-- Recomputability - we can rebuild a relevant proof given an
-- irrelevant one.

Recomputable : Set p → Set p
Recomputable P = .P → P

------------------------------------------------------------------------
-- Weak decidability
-- `nothing` is 'don't know'/'give up'; `just` is `yes`/`definitely`

WeaklyDecidable : Set p → Set p
WeaklyDecidable = Maybe
