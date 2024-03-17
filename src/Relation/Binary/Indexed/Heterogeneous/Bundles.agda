------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Relation.Binary.Indexed.Heterogeneous`.

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Indexed.Heterogeneous.Bundles where

open import Level using (suc; _⊔_)
open import Relation.Binary.Indexed.Heterogeneous.Core
open import Relation.Binary.Indexed.Heterogeneous.Structures

------------------------------------------------------------------------
-- Definitions

record IndexedSetoid {i} (I : Set i) c ℓ : Set (suc (i ⊔ c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : I → Set c
    _≈_           : IRel Carrier ℓ
    isEquivalence : IsIndexedEquivalence Carrier _≈_

  open IsIndexedEquivalence isEquivalence public


record IndexedPreorder {i} (I : Set i) c ℓ₁ ℓ₂ :
                       Set (suc (i ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≲_
  field
    Carrier    : I → Set c
    _≈_        : IRel Carrier ℓ₁  -- The underlying equality.
    _≲_        : IRel Carrier ℓ₂  -- The relation.
    isPreorder : IsIndexedPreorder Carrier _≈_ _≲_

  open IsIndexedPreorder isPreorder public

  infix 4 _∼_
  _∼_ = _≲_



------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

{-# WARNING_ON_USAGE IndexedPreorder._∼_
"Warning: IndexedPreorder._∼_ was deprecated in v2.0. Please use IndexedPreorder._≲_ instead. "
#-}
