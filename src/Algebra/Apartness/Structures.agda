------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebraic structures with an apartness relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core using (Op₁; Op₂)
open import Relation.Binary.Core using (Rel)

module Algebra.Apartness.Structures
  {c ℓ₁ ℓ₂} {Carrier : Set c}
  (_≈_ : Rel Carrier ℓ₁)
  (_#_ : Rel Carrier ℓ₂)
  (_+_ _*_ : Op₂ Carrier) (-_ : Op₁ Carrier) (0# 1# : Carrier)
  where

open import Level using (_⊔_; suc)
open import Algebra.Definitions _≈_ using (Invertible)
open import Algebra.Structures _≈_ using (IsCommutativeRing)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.Definitions
  using (LeftStronglyExtensional; RightStronglyExtensional; StronglyExtensional)
open import Relation.Binary.Structures
  using (IsEquivalence; IsApartnessRelation; IsTightApartnessRelation)
import Relation.Binary.Properties.ApartnessRelation as AR


record IsHeytingCommutativeRing : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where

  field
    isCommutativeRing        : IsCommutativeRing _+_ _*_ -_ 0# 1#
    isTightApartnessRelation : IsTightApartnessRelation _≈_ _#_
    +-stronglyExtensional    : StronglyExtensional _#_ _+_
    *-stronglyExtensional    : StronglyExtensional _#_ _*_

  open IsCommutativeRing isCommutativeRing public
  open IsTightApartnessRelation isTightApartnessRelation public
    using (isApartnessRelation; tight)
  open IsApartnessRelation isApartnessRelation public
    renaming
      ( irrefl  to #-irrefl
      ; sym     to #-sym
      ; cotrans to #-cotrans
      )

  +-stronglyExtensionalˡ : LeftStronglyExtensional _#_ _+_
  +-stronglyExtensionalˡ = +-stronglyExtensional .proj₁
  +-stronglyExtensionalʳ : RightStronglyExtensional _#_ _+_
  +-stronglyExtensionalʳ = +-stronglyExtensional .proj₂

  *-stronglyExtensionalˡ : LeftStronglyExtensional _#_ _*_
  *-stronglyExtensionalˡ = *-stronglyExtensional .proj₁
  *-stronglyExtensionalʳ : RightStronglyExtensional _#_ _*_
  *-stronglyExtensionalʳ = *-stronglyExtensional .proj₂

  ¬#-isEquivalence : IsEquivalence _¬#_
  ¬#-isEquivalence = AR.¬#-isEquivalence refl isApartnessRelation


record IsHeytingField : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where

  field
    isHeytingCommutativeRing : IsHeytingCommutativeRing

  open IsHeytingCommutativeRing isHeytingCommutativeRing public

  field
    #⇒invertible             : ∀ {x y} → x # y → Invertible 1# _*_ (x - y)
    invertible⇒#             : ∀ {x y} → Invertible 1# _*_ (x - y) → x # y

