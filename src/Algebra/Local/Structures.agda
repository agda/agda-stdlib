------------------------------------------------------------------------
-- The Agda standard library
--
-- Local algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Local.Structures where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (∃-syntax; _×_)
open import Algebra.Core using (Op₁; Op₂)
open import Algebra.Definitions using (Invertible)
open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence; IsApartness)
open import Relation.Binary.Definitions using (Tight)
import Relation.Binary.Properties.Apartness as A
open import Relation.Nullary using (¬_)


module _
  {c ℓ₁ ℓ₂} {Carrier : Set c}
  (_≈_ : Rel Carrier ℓ₁)
  (_#_ : Rel Carrier ℓ₂)
  (_+_ _*_ : Op₂ Carrier) (-_ : Op₁ Carrier) (0# 1# : Carrier)
  where

  -- private to avoid clash with Monoid._-_
  private
    _-_ : Op₂ Carrier
    x - y = x + (- y)

    Iso : ∀ {a b} → Set a → Set b → Set _
    Iso A B = (A → B) × (B → A)


  record IsLocalCommutativeRing : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isCommutativeRing : IsCommutativeRing _≈_ _+_ _*_ -_ 0# 1#
      isApartness       : IsApartness _≈_ _#_
      #⇔invertible      : ∀ {x y} → Iso (x # y) (Invertible _≈_ 1# _*_ (x - y))

    open IsCommutativeRing isCommutativeRing public
    open IsApartness isApartness public

    _¬#_ : Carrier → Carrier → Set _
    x ¬# y = ¬ (x # y)

    ¬#-equiv : IsEquivalence _¬#_
    ¬#-equiv = A.¬#-equiv refl isApartness


  record IsHeytingField : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isLocalCommutativeRing : IsLocalCommutativeRing
      isTight                : Tight _≈_ _#_

    open IsLocalCommutativeRing isLocalCommutativeRing public