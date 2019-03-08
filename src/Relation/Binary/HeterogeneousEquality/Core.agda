------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous equality
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.HeterogeneousEquality.

{-# OPTIONS --with-K --safe #-}

module Relation.Binary.HeterogeneousEquality.Core where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

------------------------------------------------------------------------
-- Heterogeneous equality

infix 4 _≅_

data _≅_ {ℓ₁} {A : Set ℓ₁} (x : A) : ∀ {ℓ₂} {B : Set ℓ₂} → B → Set ℓ₁ where
   refl : x ≅ x

------------------------------------------------------------------------
-- Conversion

≅-to-≡ : ∀ {a} {A : Set a} {x y : A} → x ≅ y → x ≡ y
≅-to-≡ refl = refl
