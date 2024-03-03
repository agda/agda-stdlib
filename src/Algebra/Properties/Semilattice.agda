------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Algebra.Lattice.Properties.Semilattice` instead.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Lattice

module Algebra.Properties.Semilattice {c ℓ} (L : Semilattice c ℓ) where

open import Algebra.Lattice.Properties.Semilattice L public

{-# WARNING_ON_IMPORT
"Algebra.Properties.Semilattice was deprecated in v2.0.
Use Algebra.Lattice.Properties.Semilattice instead."
#-}
