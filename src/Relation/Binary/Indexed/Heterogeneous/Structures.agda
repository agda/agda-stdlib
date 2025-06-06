------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via
-- `Relation.Binary.Indexed.Heterogeneous`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Indexed.Heterogeneous.Core

module Relation.Binary.Indexed.Heterogeneous.Structures
  {i a ℓ} {I : Set i} (A : I → Set a) (_≈_ : IRel A ℓ)
  where

open import Function.Base using (id; _⟨_⟩_)
open import Level using (suc; _⊔_)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Indexed.Heterogeneous.Definitions
  using (Reflexive; Symmetric; Transitive)

------------------------------------------------------------------------
-- Equivalences

record IsIndexedEquivalence : Set (i ⊔ a ⊔ ℓ) where
  field
    refl  : Reflexive  A _≈_
    sym   : Symmetric  A _≈_
    trans : Transitive A _≈_

  reflexive : ∀ {i} → _≡_ ⟨ _⇒_ ⟩ _≈_ {i}
  reflexive ≡.refl = refl


record IsIndexedPreorder {ℓ₂} (_≲_ : IRel A ℓ₂) : Set (i ⊔ a ⊔ ℓ ⊔ ℓ₂) where
  field
    isEquivalence : IsIndexedEquivalence
    reflexive     : ∀ {i j} → (_≈_ {i} {j}) ⟨ _⇒_ ⟩ _≲_
    trans         : Transitive A _≲_

  module Eq = IsIndexedEquivalence isEquivalence

  refl : Reflexive A _≲_
  refl = reflexive Eq.refl
