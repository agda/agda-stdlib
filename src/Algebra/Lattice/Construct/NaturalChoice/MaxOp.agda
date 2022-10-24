------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of a max operator derived from a spec over a total
-- preorder.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Construct.NaturalChoice.Base
import Algebra.Lattice.Construct.NaturalChoice.MinOp as MinOp
open import Relation.Binary

module Algebra.Lattice.Construct.NaturalChoice.MaxOp
  {a ℓ₁ ℓ₂} {O : TotalPreorder a ℓ₁ ℓ₂} (maxOp : MaxOperator O)
  where

private
  module Min = MinOp (MaxOp⇒MinOp maxOp)

open Min public
  using ()
  renaming
  ( ⊓-isSemilattice           to  ⊔-isSemilattice
  ; ⊓-semilattice             to  ⊔-semilattice
  )
