------------------------------------------------------------------------
-- The Agda standard library
--
-- Apartness properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)

module Relation.Binary.Properties.ApartnessRelation
  {a ℓ₁ ℓ₂} {A : Set a}
  {_≈_ : Rel A ℓ₁}
  {_#_ : Rel A ℓ₂}
  where

open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.Consequences using (sym⇒¬-sym; cotrans⇒¬-trans)
open import Relation.Binary.Structures using (IsEquivalence; IsApartnessRelation)
open import Relation.Nullary using (¬_)


private
  _¬#_ : A → A → Set _
  x ¬# y = ¬ (x # y)

¬#-isEquivalence : Reflexive _≈_ → IsApartnessRelation _≈_ _#_ → IsEquivalence _¬#_
¬#-isEquivalence re apart = record
  { refl = irrefl re
  ; sym = λ {a} {b} → sym⇒¬-sym sym {a} {b} 
  ; trans = cotrans⇒¬-trans cotrans
  } where open IsApartnessRelation apart
