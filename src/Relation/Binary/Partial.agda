------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of partial binary relations

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Partial where

open import Level
open import Relation.Binary
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Partial Equivalence relations
--
-- Equivalence relations are not defined in terms of their partial
-- counterparts for backwards-compatibility reasons.


private
  variable
    a ℓ : Level

record IsPartialEquivalence {A : Set a} (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    sym   : Symmetric _≈_
    trans : Transitive _≈_

------------------------------------------------------------------------
-- Partial Setoids

record PartialSetoid {c} (Carrier : Set c) ℓ  : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    _≈_           : Rel Carrier ℓ
    isPartialEquivalence : IsPartialEquivalence _≈_

  _≉_ : Rel Carrier _
  x ≉ y = ¬ (x ≈ y)

  open IsPartialEquivalence isPartialEquivalence public


------------------------------------------------------------------------
-- Lowering Equivalences

fromEquivalence : ∀ {A : Set a} {_≈_ : Rel A ℓ} → IsEquivalence _≈_ → IsPartialEquivalence _≈_
fromEquivalence eq = record
  { sym = sym
  ; trans = trans
  }
  where open IsEquivalence eq


fromSetoid : (S : Setoid a ℓ) → PartialSetoid (Setoid.Carrier S) ℓ
fromSetoid S = record
  { isPartialEquivalence = fromEquivalence isEquivalence }
  where open Setoid S
