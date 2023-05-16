------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of a min operator derived from a spec over a total
-- preorder.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles
open import Algebra.Lattice.Bundles
open import Algebra.Construct.NaturalChoice.Base
open import Relation.Binary

module Algebra.Lattice.Construct.NaturalChoice.MinOp
  {a ℓ₁ ℓ₂} {O : TotalPreorder a ℓ₁ ℓ₂} (minOp : MinOperator O) where

open TotalPreorder O
open MinOperator minOp

open import Algebra.Lattice.Structures _≈_
open import Algebra.Construct.NaturalChoice.MinOp minOp

------------------------------------------------------------------------
-- Structures

⊓-isSemilattice : IsSemilattice _⊓_
⊓-isSemilattice = record
  { isBand = ⊓-isBand
  ; comm   = ⊓-comm
  }

------------------------------------------------------------------------
-- Bundles

⊓-semilattice : Semilattice _ _
⊓-semilattice = record
  { isSemilattice = ⊓-isSemilattice
  }
