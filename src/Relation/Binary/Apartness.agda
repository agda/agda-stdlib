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


module Properties {c ℓ₁} {Carrier : Set c} (_#_ : Rel Carrier ℓ₁) where

  _¬#_ : Carrier → Carrier → Set _
  x ¬# y = ¬ (x # y)

  sym⇒sym-¬ : Symmetric _#_ → Symmetric _¬#_
  sym⇒sym-¬ sym# x¬#y y#x = x¬#y (sym# y#x)

  Comparison : Set _
  Comparison = ∀ {x y z} → x # z → (x # y) ⊎ (y # z)

  comp⇒trans-¬ : Comparison → Transitive _¬#_
  comp⇒trans-¬ comp x¬#y y¬#z x#z = [ x¬#y , y¬#z ]′ (comp x#z)


module Structures {c ℓ₁ ℓ₂} {Carrier : Set c} (_≈_ : Rel Carrier ℓ₁) (_#_ : Rel Carrier ℓ₂) where

  open Properties _#_

  record IsApartness : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      irrefl : Irreflexive _≈_ _#_
      sym    : Symmetric _#_
      comp   : Comparison

  irrefl⇒refl-¬ : Reflexive _≈_ → Irreflexive _≈_ _#_ → Reflexive _¬#_
  irrefl⇒refl-¬ re irr = irr re

  ¬#-equiv : Reflexive _≈_ → IsApartness → IsEquivalence _¬#_
  ¬#-equiv re apart =
    record { refl = irrefl⇒refl-¬ re irrefl ; sym = sym⇒sym-¬ sym ; trans = comp⇒trans-¬ comp }
    where open IsApartness apart

  Tight : Set _
  Tight = ∀ {x y} → (x ¬# y) × (y ¬# x) → x ≈ y


module Bundles where

  open Structures

  record Apartness (c ℓ₁ ℓ₂ : Level) : Set (lsuc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      Carrier : Set c
      _≈_ : Rel Carrier ℓ₁
      _#_ : Rel Carrier ℓ₂
      isApartness : IsApartness _≈_ _#_
      
    open IsApartness isApartness public