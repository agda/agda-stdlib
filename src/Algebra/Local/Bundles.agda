module Algebra.Local.Bundles where

open import Level using (_⊔_; suc)
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Local.Structures using (IsLocalCommutativeRing; IsHeytingField)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Apartness)

record LocalCommutativeRing c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
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


record HeytingField c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
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