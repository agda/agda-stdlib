------------------------------------------------------------------------
-- The Agda standard library
--
-- A type `A` is irrelevant if all of its elements are equal.
-- This is also refered to as "A is an h-proposition".
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Irrelevant where

open import Agda.Builtin.Equality using (_≡_)
open import Level using (Level)

private
  variable
    p : Level

Irrelevant : Set p → Set p
Irrelevant P = ∀ (p₁ p₂ : P) → p₁ ≡ p₂
