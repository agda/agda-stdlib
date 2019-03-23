------------------------------------------------------------------------
-- The Agda standard library
--
-- The max operator derived from an arbitrary total order
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Algebra.Construct.NaturalChoice.Max
  {a ℓ₁ ℓ₂} (totalOrder : TotalOrder a ℓ₁ ℓ₂) where

open import Relation.Binary.Construct.Converse using ()
  renaming (totalOrder to flip)

------------------------------------------------------------------------
-- Max is just min with a flipped order

open import Algebra.Construct.NaturalChoice.Min (flip totalOrder) public
  using
  ( cong; idem; sel; assoc; comm
  ; identityˡ; identityʳ; identity; zeroˡ; zeroʳ; zero
  ; isMagma; isSemigroup; isBand; isSemilattice; isMonoid
  ; magma; semigroup; band; semilattice; monoid
  )
  renaming
  ( min            to max
  ; min[x,y]≈y⇒y≤x to max[x,y]≈y⇒x≤y
  ; min[x,y]≈x⇒x≤y to max[x,y]≈x⇒y≤x
  )
