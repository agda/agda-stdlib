------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded meet semilattices
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Lattice.Properties.BoundedMeetSemilattice
  {c ℓ₁ ℓ₂} (M : BoundedMeetSemilattice c ℓ₁ ℓ₂) where

open BoundedMeetSemilattice M

open import Algebra.Definitions _≈_
open import Function.Base using (_∘_; flip)
open import Relation.Binary.Properties.Poset poset
import Relation.Binary.Lattice.Properties.BoundedJoinSemilattice as J

-- The dual construction is a bounded join semilattice.

dualIsBoundedJoinSemilattice : IsBoundedJoinSemilattice _≈_ (flip _≤_) _∧_ ⊤
dualIsBoundedJoinSemilattice = record
  { isJoinSemilattice = record
    { isPartialOrder  = ≥-isPartialOrder
    ; supremum        = infimum
    }
  ; minimum           = maximum
  }

dualBoundedJoinSemilattice : BoundedJoinSemilattice c ℓ₁ ℓ₂
dualBoundedJoinSemilattice = record
  { ⊥                        = ⊤
  ; isBoundedJoinSemilattice = dualIsBoundedJoinSemilattice
  }

open J dualBoundedJoinSemilattice
  hiding (dualIsBoundedMeetSemilattice; dualBoundedMeetSemilattice) public
