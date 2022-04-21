------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of right-residuated semilattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Ordered.Residuated using (RightResiduatedSemilattice)

module Relation.Binary.Lattice.Properties.RightResiduatedSemilattice
  {a ℓ₁ ℓ₂} (rrsl : RightResiduatedSemilattice a ℓ₁ ℓ₂)
  where

open RightResiduatedSemilattice rrsl

open import Algebra.Definitions _≈_ using (_DistributesOverˡ_)
import Algebra.Properties.RightResiduatedPomonoid as RightResiduatedPomonoid
open import Function.GaloisConnection using (GaloisConnection)

open RightResiduatedPomonoid rightResiduatedPomonoid

∙-∨-distribˡ : _∙_ DistributesOverˡ _∨_
∙-∨-distribˡ x y z = ∨-pres supremum supremum y z
  where open GaloisConnection (galoisConnection x)
