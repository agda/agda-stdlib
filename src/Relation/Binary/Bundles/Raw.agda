------------------------------------------------------------------------
-- The Agda standard library
--
-- Raw bundles for homogeneous binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Relation.Binary`.

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Bundles.Raw where

open import Function.Base using (flip)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary.Negation.Core using (¬_)


------------------------------------------------------------------------
-- RawSetoid
------------------------------------------------------------------------

record RawSetoid a ℓ : Set (suc (a ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier              : Set a
    _≈_                  : Rel Carrier ℓ

  infix 4 _≉_
  _≉_ : Rel Carrier _
  x ≉ y = ¬ (x ≈ y)


------------------------------------------------------------------------
-- RawRelation: basis for Relation.Binary.Bundles.*Order
------------------------------------------------------------------------

record RawRelation c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_        : Rel Carrier ℓ₂  -- The underlying relation.

  rawSetoid : RawSetoid c ℓ₁
  rawSetoid = record { _≈_ = _≈_ }

  open RawSetoid rawSetoid public
    using (_≉_)

  infix 4 _≁_
  _≁_ : Rel Carrier _
  x ≁ y = ¬ (x ∼ y)

  infix 4 _∼ᵒ_
  _∼ᵒ_ = flip _∼_

  infix 4 _≁ᵒ_
  _≁ᵒ_ = flip _≁_

