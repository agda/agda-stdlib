------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Lattice.Bundles
import Algebra.Lattice.Properties.Lattice as LatticeProperties

module Algebra.Lattice.Properties.DistributiveLattice
  {dl₁ dl₂} (DL : DistributiveLattice dl₁ dl₂)
  where

open DistributiveLattice DL
open import Algebra.Definitions _≈_
open import Algebra.Lattice.Structures _≈_
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Export properties of lattices

open LatticeProperties lattice public

------------------------------------------------------------------------
-- The dual construction is also a distributive lattice.

∧-∨-isDistributiveLattice : IsDistributiveLattice _∧_ _∨_
∧-∨-isDistributiveLattice = record
  { isLattice   = ∧-∨-isLattice
  ; ∨-distrib-∧ = ∧-distrib-∨
  ; ∧-distrib-∨ = ∨-distrib-∧
  }

∧-∨-distributiveLattice : DistributiveLattice _ _
∧-∨-distributiveLattice = record
  { isDistributiveLattice = ∧-∨-isDistributiveLattice
  }
