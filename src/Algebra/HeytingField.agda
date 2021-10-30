------------------------------------------------------------------------
-- The Agda standard library
--
-- Local commutative rings and heyting fields
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.HeytingField where

open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (∃-syntax; _×_)
import Relation.Binary.Apartness as A


module Structures
  {c ℓ₁ ℓ₂} {Carrier : Set c}
  (_≈_ : Rel Carrier ℓ₁)
  (_#_ : Rel Carrier ℓ₂)
  (_+_ _*_ : Op₂ Carrier) (-_ : Op₁ Carrier) (0# 1# : Carrier)
  where

  open A.Structures hiding (¬#-equiv)

  invertible : Carrier → Set _
  invertible x = ∃[ 1/x ] (x * 1/x) ≈ 1#


  record IsLocalCommutativeRing : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#
      isApartness : IsApartness _≈_ _#_
      #⇔invertible : ∀ {x y} → let x-y = x + (- y) in (x # y → invertible x-y) × (invertible x-y → x # y)

    open IsCommutativeRing isCommutativeRing public
    open IsApartness isApartness public

    open import Relation.Nullary using (¬_)

    _¬#_ : Carrier → Carrier → Set _
    x ¬# y = ¬ (x # y)

    ¬#-equiv : IsEquivalence _¬#_
    ¬#-equiv = A.Structures.¬#-equiv _≈_ _#_ refl isApartness


  record IsHeytingField : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLocalCommutativeRing : IsLocalCommutativeRing
      isTight : Tight _≈_ _#_

    open IsLocalCommutativeRing isLocalCommutativeRing public


module Bundles where
  open Structures
  open A.Bundles

  record LocalCommutativeRing (c ℓ₁ ℓ₂ : Level) : Set (lsuc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
    field
      Carrier                : Set c
      _≈_                    : Rel Carrier ℓ₁
      _#_                    : Rel Carrier ℓ₂
      _+_                    : Op₂ Carrier
      _*_                    : Op₂ Carrier
      -_                     : Op₁ Carrier
      0#                     : Carrier
      1#                     : Carrier
      isLocalCommutativeRing : IsLocalCommutativeRing _≈_ _#_ _+_ _*_ -_ 0# 1#

    open IsLocalCommutativeRing isLocalCommutativeRing public

    apart : Apartness c ℓ₁ ℓ₂
    apart = record { isApartness = isApartness }


  record HeytingField (c ℓ₁ ℓ₂ : Level) : Set (lsuc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
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

    apart : Apartness c ℓ₁ ℓ₂
    apart = record { isApartness = isApartness }