------------------------------------------------------------------------
-- The Agda standard library
--
-- Irrelevant types
------------------------------------------------------------------------
{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Irrelevant where

open import Agda.Builtin.Equality using (_≡_)
open import Level using (Level)

private
  variable
    p : Level
    P : Set p

Irrelevant : Set p → Set p
Irrelevant P = ∀ (p₁ p₂ : P) → p₁ ≡ p₂
