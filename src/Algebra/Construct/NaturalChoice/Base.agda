------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic definition of an operator that computes the min/max value
-- with respect to a total preorder.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core using (Op₂)
open import Level as L hiding (_⊔_)
open import Function.Base using (flip)
open import Relation.Binary.Bundles using (TotalPreorder)
open import Relation.Binary.Construct.Flip.EqAndOrd using ()
  renaming (totalPreorder to flipOrder)
import Relation.Binary.Properties.TotalOrder as TotalOrderProperties

module Algebra.Construct.NaturalChoice.Base where

private
  variable
    a ℓ₁ ℓ₂ : Level
    O : TotalPreorder a ℓ₁ ℓ₂

------------------------------------------------------------------------
-- Definition

module _ (O : TotalPreorder a ℓ₁ ℓ₂) where
  open TotalPreorder O renaming (_≲_ to _≤_)
  private _≥_ = flip _≤_

  record MinOperator : Set (a L.⊔ ℓ₁ L.⊔ ℓ₂) where
    infixl 7 _⊓_
    field
      _⊓_       : Op₂ Carrier
      x≤y⇒x⊓y≈x : ∀ {x y} → x ≤ y → x ⊓ y ≈ x
      x≥y⇒x⊓y≈y : ∀ {x y} → x ≥ y → x ⊓ y ≈ y

  record MaxOperator : Set (a L.⊔ ℓ₁ L.⊔ ℓ₂) where
    infixl 6 _⊔_
    field
      _⊔_       : Op₂ Carrier
      x≤y⇒x⊔y≈y : ∀ {x y} → x ≤ y → x ⊔ y ≈ y
      x≥y⇒x⊔y≈x : ∀ {x y} → x ≥ y → x ⊔ y ≈ x

------------------------------------------------------------------------
-- Properties

MinOp⇒MaxOp : MinOperator O → MaxOperator (flipOrder O)
MinOp⇒MaxOp minOp = record
  { _⊔_       = _⊓_
  ; x≤y⇒x⊔y≈y = x≥y⇒x⊓y≈y
  ; x≥y⇒x⊔y≈x = x≤y⇒x⊓y≈x
  } where open MinOperator minOp

MaxOp⇒MinOp : MaxOperator O → MinOperator (flipOrder O)
MaxOp⇒MinOp maxOp = record
  { _⊓_       = _⊔_
  ; x≤y⇒x⊓y≈x = x≥y⇒x⊔y≈x
  ; x≥y⇒x⊓y≈y = x≤y⇒x⊔y≈y
  } where open MaxOperator maxOp
