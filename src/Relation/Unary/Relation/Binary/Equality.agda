------------------------------------------------------------------------
-- The Agda standard library
--
-- Equality of unary relations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Relation.Binary.Equality where

open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Unary using (Pred; _≐_; _≐′_)
open import Relation.Unary.Properties

private
  variable
    a ℓ : Level
    A : Set a

≐-isEquivalence : IsEquivalence {A = Pred A ℓ} _≐_
≐-isEquivalence = record
  { refl = ≐-refl
  ; sym = ≐-sym
  ; trans = ≐-trans
  }

≐′-isEquivalence : IsEquivalence {A = Pred A ℓ} _≐′_
≐′-isEquivalence = record
  { refl = ≐′-refl
  ; sym = ≐′-sym
  ; trans = ≐′-trans
  }

≐-setoid : ∀ {a} (A : Set a) ℓ → Setoid _ _
≐-setoid A ℓ = record
  { isEquivalence = ≐-isEquivalence {A = A} {ℓ}
  }

≐′-setoid : ∀ {a} (A : Set a) ℓ → Setoid _ _
≐′-setoid A ℓ = record
  { isEquivalence = ≐′-isEquivalence {A = A} {ℓ}
  }
