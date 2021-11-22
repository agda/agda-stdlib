------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by meet semilattices
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.MeetSemilattice
  {c ℓ₁ ℓ₂} (M : MeetSemilattice c ℓ₁ ℓ₂) where

open import Relation.Binary.Lattice.Properties.MeetSemilattice M public

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.MeetSemilattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.MeetSemilattice instead."
#-}

