------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic structures with an apartness relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Apartness.Structures where

open import Algebra.Core using (Op₁; Op₂)
open import Relation.Binary.Core using (Rel)
open import Level using (_⊔_; suc)
open import Data.Product using (∃-syntax; _×_; _,_; proj₂)
open import Algebra.Definitions using (Invertible)
open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.Structures using (IsEquivalence; IsApartnessRelation)
open import Relation.Binary.Definitions using (Tight)
open import Relation.Nullary using (¬_)
import Relation.Binary.Properties.ApartnessRelation as ApartnessRelation


private
  Iso : ∀ {a b} → Set a → Set b → Set _
  Iso A B = (A → B) × (B → A)


record IsHeytingCommutativeRing
  {c ℓ₁ ℓ₂} {Carrier : Set c}
  (_≈_ : Rel Carrier ℓ₁)
  (_#_ : Rel Carrier ℓ₂)
  (_+_ _*_ : Op₂ Carrier) (-_ : Op₁ Carrier) (0# 1# : Carrier)
  : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where

  field
    isCommutativeRing   : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#
    isApartnessRelation : IsApartnessRelation _≈_ _#_

  open IsCommutativeRing isCommutativeRing public
  open IsApartnessRelation isApartnessRelation public

  field
    #⇔invertible : ∀ {x y} → Iso (x # y) (Invertible _≈_ 1# _*_ (x - y))

  ¬#-isEquivalence : IsEquivalence _¬#_
  ¬#-isEquivalence = ApartnessRelation.¬#-isEquivalence refl isApartnessRelation


record IsHeytingField
  {c ℓ₁ ℓ₂} {Carrier : Set c}
  (_≈_ : Rel Carrier ℓ₁)
  (_#_ : Rel Carrier ℓ₂)
  (_+_ _*_ : Op₂ Carrier) (-_ : Op₁ Carrier) (0# 1# : Carrier)
  : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where

  field
    isHeytingCommutativeRing : IsHeytingCommutativeRing _≈_ _#_ _+_ _*_ -_ 0# 1#
    tight                    : Tight _≈_ _#_

  open IsHeytingCommutativeRing isHeytingCommutativeRing public
