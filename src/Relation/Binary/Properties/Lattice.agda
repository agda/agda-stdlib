------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Relation.Binary.Lattice.Properties.Lattice` instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Properties.Lattice
  {c ℓ₁ ℓ₂} (L : Lattice c ℓ₁ ℓ₂) where

open import Relation.Binary.Lattice.Properties.Lattice L public

{-# WARNING_ON_IMPORT
"Relation.Binary.Properties.Lattice was deprecated in v2.0.
Use Relation.Binary.Lattice.Properties.Lattice instead."
#-}
