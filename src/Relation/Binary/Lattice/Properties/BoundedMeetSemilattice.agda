------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded meet semilattices
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice
  using (BoundedMeetSemilattice; IsBoundedJoinSemilattice; BoundedJoinSemilattice)

module Relation.Binary.Lattice.Properties.BoundedMeetSemilattice
  {c ℓ₁ ℓ₂} (M : BoundedMeetSemilattice c ℓ₁ ℓ₂) where

open import Function.Base using (_∘_; flip)

open BoundedMeetSemilattice M
  using (⊤; _∧_; isBoundedMeetSemilattice; _≈_; poset; _≤_; infimum; maximum)

open import Algebra.Definitions _≈_
  using (LeftIdentity; RightIdentity; Identity)
open import Relation.Binary.Properties.Poset poset using (≥-isPartialOrder)
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

