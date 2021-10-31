------------------------------------------------------------------------
-- The Agda standard library
--
-- Apartness relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Apartness where

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Symmetric; Transitive; Reflexive; Irreflexive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; [_,_]′)
open import Data.Product using (_×_)


module Bundles where

  open Structures

  record Apartness (c ℓ₁ ℓ₂ : Level) : Set (lsuc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      Carrier : Set c
      _≈_ : Rel Carrier ℓ₁
      _#_ : Rel Carrier ℓ₂
      isApartness : IsApartness _≈_ _#_
      
    open IsApartness isApartness public