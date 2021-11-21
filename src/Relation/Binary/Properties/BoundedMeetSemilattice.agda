------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded meet semilattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.BoundedMeetSemilattice
  {c ℓ₁ ℓ₂} (M : BoundedMeetSemilattice c ℓ₁ ℓ₂) where

open BoundedMeetSemilattice M

open import Relation.Binary.Lattice.Properties.BoundedMeetSemilattice

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.BoundedMeetSemilattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.BoundedMeetSemilattice instead."
#-}
