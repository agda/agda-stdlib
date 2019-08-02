------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of homogeneous partial equivalence relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Partial where

open import Level
open import Relation.Binary using (Setoid)
open import Relation.Nullary using ( ¬_)

------------------------------------------------------------------------
-- Simple properties and equivalence relations

open import Relation.Binary.Core public

------------------------------------------------------------------------
-- Equivalence relations

record IsPartialEquivalence {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    sym   : Symmetric _≈_
    trans : Transitive _≈_

------------------------------------------------------------------------
-- Partial Setoids

record PartialSetoid c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    Carrier         : Set c
    _≈_             : Rel Carrier ℓ
    isPartialEquivalence : IsPartialEquivalence _≈_

  _≉_ : Rel Carrier _
  x ≉ y = ¬ (x ≈ y)

  open IsPartialEquivalence isPartialEquivalence public

------------------------------------------------------------------------
-- Lowering Equivalences

fromEquivalence : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} → IsEquivalence _≈_ → IsPartialEquivalence _≈_
fromEquivalence eq = record
  { sym = sym
  ; trans = trans
  }
  where open IsEquivalence eq

fromSetoid : ∀ {c ℓ} → Setoid c ℓ → PartialSetoid c ℓ
fromSetoid S = record
  { Carrier = Carrier
  ; _≈_ = _≈_
  ; isPartialEquivalence = fromEquivalence isEquivalence
  }
  where open Setoid S
