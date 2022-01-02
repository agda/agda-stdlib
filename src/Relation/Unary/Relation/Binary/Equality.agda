------------------------------------------------------------------------
-- The Agda standard library
--
-- Equality of unary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Unary.Relation.Binary.Equality where

open import Level using (Level)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Unary using (Pred; _≐_; _≐′_)
open import Relation.Unary.Properties

private
  variable
    a ℓ₁ ℓ₂ : Level
    A : Set a

≐-isEquivalence : IsEquivalence {A = Pred A ℓ₁} _≐_
≐-isEquivalence = record
  { refl = ≐-refl
  ; sym = ≐-sym
  ; trans = ≐-trans
  }

≐′-isEquivalence : IsEquivalence {A = Pred A ℓ₁} _≐′_
≐′-isEquivalence = record
  { refl = ≐′-refl
  ; sym = ≐′-sym
  ; trans = ≐′-trans
  }
