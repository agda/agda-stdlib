------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional (intensional) equality:
--   Equivalence, Order, Setoid
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.PropositionalEquality.Bundles where

open import Function.Base using (id)
open import Level using (Level)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Structure of equality as a binary relation

isEquivalence : IsEquivalence {A = A} _≡_
isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

isDecEquivalence : Decidable _≡_ → IsDecEquivalence {A = A} _≡_
isDecEquivalence _≟_ = record
  { isEquivalence = isEquivalence
  ; _≟_           = _≟_
  }

isPreorder : IsPreorder {A = A} _≡_ _≡_
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = id
  ; trans         = trans
  }

------------------------------------------------------------------------
-- Bundles for equality as a binary relation

setoid : Set a → Setoid _ _
setoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; isEquivalence = isEquivalence
  }

decSetoid : Decidable {A = A} _≡_ → DecSetoid _ _
decSetoid _≟_ = record
  { _≈_              = _≡_
  ; isDecEquivalence = isDecEquivalence _≟_
  }

preorder : Set a → Preorder _ _ _
preorder A = record
  { Carrier    = A
  ; _≈_        = _≡_
  ; _∼_        = _≡_
  ; isPreorder = isPreorder
  }
