------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties for distributive lattice
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.DistributiveLattice
  {c ℓ₁ ℓ₂} (L : DistributiveLattice c ℓ₁ ℓ₂) where

open import Relation.Binary.Lattice.Properties.DistributiveLattice L public

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.DistributiveLattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.DistributiveLattice instead."
#-}
