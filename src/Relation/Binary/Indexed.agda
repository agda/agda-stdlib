------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed binary relations
------------------------------------------------------------------------

module Relation.Binary.Indexed where

open import Function
open import Level using (suc; _⊔_)
import Relation.Binary as B
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)

------------------------------------------------------------------------
-- Publically export core definitions

open import Relation.Binary.Indexed.Core public

------------------------------------------------------------------------
-- Equivalences

record IsIndexedEquivalence {i a ℓ} {I : Set i} (A : I → Set a)
                            (_≈_ : Rel A ℓ) : Set (i ⊔ a ⊔ ℓ) where
  field
    refl  : Reflexive  A _≈_
    sym   : Symmetric  A _≈_
    trans : Transitive A _≈_

  reflexive : ∀ {i} → _≡_ ⟨ B._⇒_ ⟩ _≈_ {i}
  reflexive P.refl = refl

record IndexedSetoid {i} (I : Set i) c ℓ : Set (suc (i ⊔ c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : I → Set c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsIndexedEquivalence Carrier _≈_

  open IsIndexedEquivalence isEquivalence public

------------------------------------------------------------------------
-- Preorders

record IsIndexedPreorder {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a)
                         (_≈_ : Rel A ℓ₁) (_∼_ : Rel A ℓ₂) :
                         Set (i ⊔ a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsIndexedEquivalence A _≈_
    reflexive     : ∀ {i j} → (_≈_ {i} {j}) ⟨ B._⇒_ ⟩ _∼_
    trans         : Transitive A _∼_

  module Eq = IsIndexedEquivalence isEquivalence

  refl : Reflexive A _∼_
  refl = reflexive Eq.refl

record IndexedPreorder {i} (I : Set i) c ℓ₁ ℓ₂ :
                       Set (suc (i ⊔ c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : I → Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_        : Rel Carrier ℓ₂  -- The relation.
    isPreorder : IsIndexedPreorder Carrier _≈_ _∼_

  open IsIndexedPreorder isPreorder public

------------------------------------------------------------------------
-- Convert indexed structures to non-indexed structures

isIndexedEquivalenceAt : ∀ {i a ℓ} {I : Set i} {A : I → Set a}
                         {_≈_ : Rel A ℓ} → IsIndexedEquivalence A _≈_ →
                         (x : I) → B.IsEquivalence (_≈_ {x})
isIndexedEquivalenceAt isEq i = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }
  where open IsIndexedEquivalence isEq

indexedSetoidAt : ∀ {i a ℓ} {I : Set i} → IndexedSetoid I a ℓ → I → B.Setoid a ℓ
indexedSetoidAt S i = record
  { Carrier       = Carrier i
  ; _≈_           = _≈_
  ; isEquivalence = isIndexedEquivalenceAt isEquivalence i
  }
  where open IndexedSetoid S

isIndexedPreorderAt : ∀ {i a ℓ₁ ℓ₂} {I : Set i} {A : I → Set a} {_≈_ :
                      Rel A ℓ₁} {_∼_ : Rel A ℓ₂} → IsIndexedPreorder A
                      _≈_ _∼_ → (x : I) → B.IsPreorder (_≈_ {x}) _∼_
isIndexedPreorderAt isPreorder i = record
  { isEquivalence = isIndexedEquivalenceAt isEquivalence i
  ; reflexive     = reflexive
  ; trans         = trans
  }
  where open IsIndexedPreorder isPreorder

indexedPreorderAt : ∀ {i a ℓ₁ ℓ₂} {I : Set i} → IndexedPreorder I a ℓ₁ ℓ₂ →
                    I → B.Preorder a ℓ₁ ℓ₂
indexedPreorderAt O i = record
  { Carrier    = Carrier i
  ; _≈_        = _≈_
  ; _∼_        = _∼_
  ; isPreorder = isIndexedPreorderAt isPreorder i
  }
  where open IndexedPreorder O

------------------------------------------------------------------------
-- Convert non-indexed structures to indexed structures

trivialIsIndexedEquivalence : ∀ {a ℓ} {A : Set a} {_≈_ : B.Rel A ℓ} →
                              B.IsEquivalence _≈_ →
                              ∀ {i} {I : Set i} →
                              IsIndexedEquivalence (λ (_ : I) → A) _≈_
trivialIsIndexedEquivalence isEq = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }
  where open B.IsEquivalence isEq

trivialIndexedSetoid : ∀ {a ℓ} → B.Setoid a ℓ →
                       ∀ {i} {I : Set i} → IndexedSetoid I a ℓ
trivialIndexedSetoid S = record
  { isEquivalence = trivialIsIndexedEquivalence isEquivalence
  }
  where open B.Setoid S

trivialIsIndexedPreorder : ∀ {a ℓ₁ ℓ₂} {A : Set a}
                           {_≈_ : B.Rel A ℓ₁} {_∼_ : B.Rel A ℓ₂} →
                           B.IsPreorder _≈_ _∼_ →
                           ∀ {i} {I : Set i} →
                           IsIndexedPreorder (λ (_ : I) → A) _≈_ _∼_
trivialIsIndexedPreorder isPreorder = record
  { isEquivalence = trivialIsIndexedEquivalence isEquivalence
  ; reflexive     = reflexive
  ; trans         = trans
  }
  where open B.IsPreorder isPreorder

trivialIndexedPreorder : ∀ {a ℓ₁ ℓ₂} → B.Preorder a ℓ₁ ℓ₂ →
                         ∀ {i} {I : Set i} → IndexedPreorder I a ℓ₁ ℓ₂
trivialIndexedPreorder O = record
  { isPreorder = trivialIsIndexedPreorder isPreorder
  }
  where open B.Preorder O

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.17

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
{-
_at_ = trivialIndexedSetoid
{-# WARNING_ON_USAGE _at_
"Warning: _at_ was deprecated in v0.17.
Please use trivialIndexedSetoid instead."
#-}
-}
