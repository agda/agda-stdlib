------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded join semilattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.BoundedJoinSemilattice
  {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open BoundedJoinSemilattice J

open import Relation.Binary.Lattice.Properties.BoundedJoinSemilattice

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.BoundedJoinSemilattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.BoundedJoinSemilattice instead."
#-}
