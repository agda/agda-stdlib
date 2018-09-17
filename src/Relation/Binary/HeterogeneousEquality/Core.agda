------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous equality
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.HeterogeneousEquality.

module Relation.Binary.HeterogeneousEquality.Core where

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

------------------------------------------------------------------------
-- Heterogeneous equality

infix 4 _≅_

data _≅_ {ℓ} {A : Set ℓ} (x : A) : {B : Set ℓ} → B → Set ℓ where
   refl : x ≅ x

------------------------------------------------------------------------
-- Conversion

≅-to-≡ : ∀ {a} {A : Set a} {x y : A} → x ≅ y → x ≡ y
≅-to-≡ refl = refl
