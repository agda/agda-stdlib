------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous equality
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.HeterogeneousEquality.

{-# OPTIONS --with-K --safe #-}

module Relation.Binary.HeterogeneousEquality.Core where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

private
  variable
    a b : Level
    A : Set a

------------------------------------------------------------------------
-- Heterogeneous equality

infix 4 _≅_

data _≅_ {A : Set a} (x : A) : {B : Set b} → B → Set a where
   refl : x ≅ x

------------------------------------------------------------------------
-- Conversion

≅-to-≡ : ∀ {x y : A} → x ≅ y → x ≡ y
≅-to-≡ refl = refl

≡-to-≅ : ∀ {x y : A} → x ≡ y → x ≅ y
≡-to-≅ refl = refl
