{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Relation.Binary
open import Level using (_⊔_)

module Algebra.Properties.HeytingField where

open import Relation.Binary.Apartness
open import Data.Product using (∃-syntax)

module _
  {a r1} {A : Set a}
  (_≈_ : Rel A r1)
  (_+_ _*_ _/_ : Op₂ A) (-_ : Op₁ A) (0# 1# : A)
  where


  _#_ : A → A → Set _
  x # y = ∃[ z ] (z * (x + (- y))) ≈ 1#


  record IsLocalRing : Set (a ⊔ r1) where
    field
      isRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#
      isApartness : IsApartness _#_ _≈_

    open IsCommutativeRing isRing public
    open IsApartness isApartness public



  record IsHeytingField : Set (a ⊔ r1) where
    field
      isLocalRing : IsLocalRing
      isTight : Tight _≈_ _#_

    open IsLocalRing isLocalRing public
