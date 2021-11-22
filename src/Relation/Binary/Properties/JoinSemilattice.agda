------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by join semilattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.JoinSemilattice
  {c ℓ₁ ℓ₂} (J : JoinSemilattice c ℓ₁ ℓ₂) where

open import Relation.Binary.Lattice.Properties.JoinSemilattice J public

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.JoinSemilattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.JoinSemilattice instead."
#-}
