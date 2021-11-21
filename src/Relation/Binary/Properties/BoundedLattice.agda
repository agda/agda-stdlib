------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded lattice
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.BoundedLattice
  {c ℓ₁ ℓ₂} (L : BoundedLattice c ℓ₁ ℓ₂) where

open BoundedLattice L

open import Relation.Binary.Lattice.Properties.BoundedLattice

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.BoundedLattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.BoundedLattice instead."
#-}
