------------------------------------------------------------------------
-- The Agda standard library
--
-- The min operator derived from an arbitrary total preorder.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (TotalOrder)

module Algebra.Construct.NaturalChoice.Min
  {a ℓ₁ ℓ₂} (O : TotalOrder a ℓ₁ ℓ₂)
  where

open import Algebra.Core using (Op₂)
open import Algebra.Construct.NaturalChoice.Base
import Algebra.Construct.NaturalChoice.MinOp as MinOp
open import Data.Sum.Base using (inj₁; inj₂; [_,_])
open import Data.Product.Base using (_,_)
open import Function.Base using (id)
open TotalOrder O renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition

infixl 7 _⊓_

_⊓_ : Op₂ A
x ⊓ y with total x y
... | inj₁ x≤y = x
... | inj₂ y≤x = y

------------------------------------------------------------------------
-- Properties

x≤y⇒x⊓y≈x : ∀ {x y} → x ≤ y → x ⊓ y ≈ x
x≤y⇒x⊓y≈x {x} {y} x≤y with total x y
... | inj₁ _   = Eq.refl
... | inj₂ y≤x = antisym y≤x x≤y

x≤y⇒y⊓x≈x : ∀ {x y} → x ≤ y → y ⊓ x ≈ x
x≤y⇒y⊓x≈x {x} {y} x≤y with total y x
... | inj₁ y≤x = antisym y≤x x≤y
... | inj₂ _   = Eq.refl

minOperator : MinOperator totalPreorder
minOperator = record
  { x≤y⇒x⊓y≈x = x≤y⇒x⊓y≈x
  ; x≥y⇒x⊓y≈y = x≤y⇒y⊓x≈x
  }

open MinOp minOperator public
