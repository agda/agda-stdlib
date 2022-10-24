------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Relation.Binary.Lattice.Properties.BoundedJoinSemilattice` instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.BoundedJoinSemilattice
  {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open import Relation.Binary.Lattice.Properties.BoundedJoinSemilattice J public

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.BoundedJoinSemilattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.BoundedJoinSemilattice instead."
#-}
