------------------------------------------------------------------------
-- The Agda standard library
--
-- Nullary irrelevance
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Irrelevant where

open import Relation.Binary.PropositionalEquality

Irrelevant : ∀ {p} → Set p → Set p
Irrelevant P = ∀ (p₁ p₂ : P) → p₁ ≡ p₂
