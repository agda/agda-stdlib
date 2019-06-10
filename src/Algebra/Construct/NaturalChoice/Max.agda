------------------------------------------------------------------------
-- The Agda standard library
--
-- The max operator derived from an arbitrary total order
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Algebra.Construct.NaturalChoice.Max
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

open import Algebra.FunctionProperties
open import Relation.Binary.Construct.Converse using ()
  renaming (totalOrder to flip)

open TotalOrder totalOrder renaming (Carrier to A)

------------------------------------------------------------------------
-- Max is just min with a flipped order

import Algebra.Construct.NaturalChoice.Min (flip totalOrder) as Min

infixl 6 _⊔_

_⊔_ : Op₂ A
_⊔_ = Min._⊓_

open Min public using ()
  renaming
  ( ⊓-cong             to ⊔-cong
  ; ⊓-idem             to ⊔-idem
  ; ⊓-sel              to ⊔-sel
  ; ⊓-assoc            to ⊔-assoc
  ; ⊓-comm             to ⊔-comm
  ; ⊓-identityˡ        to ⊔-identityˡ
  ; ⊓-identityʳ        to ⊔-identityʳ
  ; ⊓-identity         to ⊔-identity
  ; ⊓-zeroˡ            to ⊔-zeroˡ
  ; ⊓-zeroʳ            to ⊔-zeroʳ
  ; ⊓-zero             to ⊔-zero
  ; ⊓-isMagma          to ⊔-isMagma
  ; ⊓-isSemigroup      to ⊔-isSemigroup
  ; ⊓-isBand           to ⊔-isBand
  ; ⊓-isSemilattice    to ⊔-isSemilattice
  ; ⊓-isMonoid         to ⊔-isMonoid
  ; ⊓-isSelectiveMagma to ⊔-isSelectiveMagma
  ; ⊓-magma            to ⊔-magma
  ; ⊓-semigroup        to ⊔-semigroup
  ; ⊓-band             to ⊔-band
  ; ⊓-semilattice      to ⊔-semilattice
  ; ⊓-monoid           to ⊔-monoid
  ; ⊓-selectiveMagma   to ⊔-selectiveMagma
  ; x⊓y≈y⇒y≤x          to x⊔y≈y⇒x≤y
  ; x⊓y≈x⇒x≤y          to x⊔y≈x⇒y≤x
  )
