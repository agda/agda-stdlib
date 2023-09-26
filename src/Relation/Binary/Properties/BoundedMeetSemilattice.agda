------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Relation.Binary.Lattice.Properties.BoundedMeetSemilattice` instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.BoundedMeetSemilattice
  {c ℓ₁ ℓ₂} (M : BoundedMeetSemilattice c ℓ₁ ℓ₂) where

open import Relation.Binary.Lattice.Properties.BoundedMeetSemilattice M public

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.BoundedMeetSemilattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.BoundedMeetSemilattice instead."
#-}
