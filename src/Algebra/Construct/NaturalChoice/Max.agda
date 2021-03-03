------------------------------------------------------------------------
-- The Agda standard library
--
-- The max operator derived from an arbitrary total order
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Algebra.Construct.NaturalChoice.Max
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

open import Algebra.Core
open import Algebra.Definitions
open import Algebra.Construct.NaturalChoice.Base
open import Relation.Binary.Construct.Converse using ()
  renaming (totalOrder to flip)

open TotalOrder totalOrder renaming (Carrier to A)

------------------------------------------------------------------------
-- Max is just min with a flipped order

import Algebra.Construct.NaturalChoice.Min (flip totalOrder) as Min

infixl 6 _⊔_

_⊔_ : Op₂ A
_⊔_ = Min._⊓_

------------------------------------------------------------------------
-- Properties

open Min public using ()
  renaming
  ( x≤y⇒x⊓y≈x to x≤y⇒y⊔x≈y
  ; x≤y⇒y⊓x≈x to x≤y⇒x⊔y≈y
  )

maxOperator : MaxOperator totalPreorder
maxOperator = record
  { x≤y⇒x⊔y≈y = x≤y⇒x⊔y≈y
  ; x≥y⇒x⊔y≈x = x≤y⇒y⊔x≈y
  }

open import Algebra.Construct.NaturalChoice.MaxOp maxOperator public
