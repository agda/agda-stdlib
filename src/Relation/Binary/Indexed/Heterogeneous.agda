------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Indexed.Heterogeneous where

open import Function
open import Level using (suc; _⊔_)
open import Relation.Binary using (_⇒_)
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)

------------------------------------------------------------------------
-- Publically export core definitions

open import Relation.Binary.Indexed.Heterogeneous.Core public

------------------------------------------------------------------------
-- Equivalences

record IsIndexedEquivalence {i a ℓ} {I : Set i} (A : I → Set a)
                            (_≈_ : IRel A ℓ) : Set (i ⊔ a ⊔ ℓ) where
  field
    refl  : Reflexive  A _≈_
    sym   : Symmetric  A _≈_
    trans : Transitive A _≈_

  reflexive : ∀ {i} → _≡_ ⟨ _⇒_ ⟩ _≈_ {i}
  reflexive P.refl = refl

record IndexedSetoid {i} (I : Set i) c ℓ : Set (suc (i ⊔ c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : I → Set c
    _≈_           : IRel Carrier ℓ
    isEquivalence : IsIndexedEquivalence Carrier _≈_

  open IsIndexedEquivalence isEquivalence public

------------------------------------------------------------------------
-- Preorders

record IsIndexedPreorder {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a)
                         (_≈_ : IRel A ℓ₁) (_∼_ : IRel A ℓ₂) :
                         Set (i ⊔ a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsIndexedEquivalence A _≈_
    reflexive     : ∀ {i j} → (_≈_ {i} {j}) ⟨ _⇒_ ⟩ _∼_
    trans         : Transitive A _∼_

  module Eq = IsIndexedEquivalence isEquivalence

  refl : Reflexive A _∼_
  refl = reflexive Eq.refl

record IndexedPreorder {i} (I : Set i) c ℓ₁ ℓ₂ :
                       Set (suc (i ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : I → Set c
    _≈_        : IRel Carrier ℓ₁  -- The underlying equality.
    _∼_        : IRel Carrier ℓ₂  -- The relation.
    isPreorder : IsIndexedPreorder Carrier _≈_ _∼_

  open IsIndexedPreorder isPreorder public

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.17

REL = IREL
{-# WARNING_ON_USAGE REL
"Warning: REL was deprecated in v0.17.
Please use IREL instead."
#-}
Rel = IRel
{-# WARNING_ON_USAGE Rel
"Warning: Rel was deprecated in v0.17.
Please use IRel instead."
#-}
Setoid = IndexedSetoid
{-# WARNING_ON_USAGE Setoid
"Warning: Setoid was deprecated in v0.17.
Please use IndexedSetoid instead."
#-}
IsEquivalence = IsIndexedEquivalence
{-# WARNING_ON_USAGE IsEquivalence
"Warning: IsEquivalence was deprecated in v0.17.
Please use IsIndexedEquivalence instead."
#-}
