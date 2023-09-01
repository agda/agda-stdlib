------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for local algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Apartness.Bundles where

open import Level using (_⊔_; suc)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (ApartnessRelation)
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Apartness.Structures

record HeytingCommutativeRing c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_ _#_
  field
    Carrier                  : Set c
    _≈_                      : Rel Carrier ℓ₁
    _#_                      : Rel Carrier ℓ₂
    _+_                      : Op₂ Carrier
    _*_                      : Op₂ Carrier
    -_                       : Op₁ Carrier
    0#                       : Carrier
    1#                       : Carrier
    isHeytingCommutativeRing : IsHeytingCommutativeRing _≈_ _#_ _+_ _*_ -_ 0# 1#

  open IsHeytingCommutativeRing isHeytingCommutativeRing public

  commutativeRing : CommutativeRing c ℓ₁
  commutativeRing = record { isCommutativeRing = isCommutativeRing }

  apartnessRelation : ApartnessRelation c ℓ₁ ℓ₂
  apartnessRelation = record { isApartnessRelation = isApartnessRelation }


record HeytingField c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix  8 -_
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_ _#_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ₁
    _#_            : Rel Carrier ℓ₂
    _+_            : Op₂ Carrier
    _*_            : Op₂ Carrier
    -_             : Op₁ Carrier
    0#             : Carrier
    1#             : Carrier
    isHeytingField : IsHeytingField _≈_ _#_ _+_ _*_ -_ 0# 1#

  open IsHeytingField isHeytingField public

  heytingCommutativeRing : HeytingCommutativeRing c ℓ₁ ℓ₂
  heytingCommutativeRing = record { isHeytingCommutativeRing = isHeytingCommutativeRing }

  apartnessRelation : ApartnessRelation c ℓ₁ ℓ₂
  apartnessRelation = record { isApartnessRelation = isApartnessRelation }
