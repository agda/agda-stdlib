------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Relation.Binary.Lattice.Properties.BoundedLattice` instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.BoundedLattice
  {c ℓ₁ ℓ₂} (L : BoundedLattice c ℓ₁ ℓ₂) where

open import Relation.Binary.Lattice.Properties.BoundedLattice L public

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.BoundedLattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.BoundedLattice instead."
#-}
