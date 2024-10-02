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
-- RawPreorder
------------------------------------------------------------------------

record RawPreorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≲_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _≲_        : Rel Carrier ℓ₂  -- The relation.

  rawSetoid : RawSetoid c ℓ₁
  rawSetoid = record { _≈_ = _≈_ }

  open RawSetoid rawSetoid public
    using (_≉_)

  infix 4 _⋦_
  _⋦_ : Rel Carrier _
  x ⋦ y = ¬ (x ≲ y)

  infix 4 _≳_
  _≳_ = flip _≲_

  infix 4 _⋧_
  _⋧_ = flip _⋦_


------------------------------------------------------------------------
-- RawPartialOrders
------------------------------------------------------------------------

record RawPartialOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ₁
    _≤_            : Rel Carrier ℓ₂

  rawPreorder : RawPreorder c ℓ₁ ℓ₂
  rawPreorder = record { _≈_ = _≈_ ; _≲_ = _≤_ }

  open RawPreorder rawPreorder public
    hiding (Carrier; _≈_; _≲_)
    renaming (_⋦_ to _≰_; _≳_ to _≥_; _⋧_ to _≱_)


record RawStrictPartialOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _<_
  field
    Carrier              : Set c
    _≈_                  : Rel Carrier ℓ₁
    _<_                  : Rel Carrier ℓ₂

  rawSetoid : RawSetoid c ℓ₁
  rawSetoid = record { _≈_ = _≈_ }

  open RawSetoid rawSetoid public
    using (_≉_)

  infix 4 _≮_
  _≮_ : Rel Carrier _
  x ≮ y = ¬ (x < y)

  infix 4 _>_
  _>_ = flip _<_

  infix 4 _≯_
  _≯_ = flip _≮_


------------------------------------------------------------------------
-- RawApartnessRelation
------------------------------------------------------------------------

record RawApartnessRelation c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _#_
  field
    Carrier             : Set c
    _≈_                 : Rel Carrier ℓ₁
    _#_                 : Rel Carrier ℓ₂

  infix 4 _¬#_
  _¬#_ : Rel Carrier _
  x ¬# y = ¬ (x # y)
