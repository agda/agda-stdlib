------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of residuated semilattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Ordered.Residuated using (ResiduatedSemilattice)

module Relation.Binary.Lattice.Properties.ResiduatedSemilattice
  {a ℓ₁ ℓ₂} (rsl : ResiduatedSemilattice a ℓ₁ ℓ₂)
  where

open ResiduatedSemilattice rsl

open import Algebra.Definitions _≈_ using (_DistributesOver_)
open import Data.Product using (_,_)
import Relation.Binary.Lattice.Properties.RightResiduatedSemilattice
  as RightResiduatedSemilattice

open RightResiduatedSemilattice rightResiduatedSemilattice
open RightResiduatedSemilattice leftResiduatedSemilattice public
  using () renaming (∙-∨-distribˡ to ∙-∨-distribʳ)

∙-∨-distrib : _∙_ DistributesOver _∨_
∙-∨-distrib = ∙-∨-distribˡ , ∙-∨-distribʳ
