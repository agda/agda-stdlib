------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by bounded join semilattices
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Lattice.Properties.BoundedJoinSemilattice
  {c ℓ₁ ℓ₂} (J : BoundedJoinSemilattice c ℓ₁ ℓ₂) where

open BoundedJoinSemilattice J

open import Algebra.Definitions _≈_
open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_; flip)
open import Relation.Binary.Properties.Poset poset
open import Relation.Binary.Lattice.Properties.JoinSemilattice joinSemilattice
  using (∨-comm)

-- Bottom is an identity of the meet operation.

identityˡ : LeftIdentity ⊥ _∨_
identityˡ x =
  let _ , x≤⊥∨x , least = supremum ⊥ x
  in antisym (least x (minimum x) refl) x≤⊥∨x

identityʳ : RightIdentity ⊥ _∨_
identityʳ x =
  let x≤x∨⊥ , _ , least = supremum x ⊥
  in antisym (least x refl (minimum x)) x≤x∨⊥

identity : Identity ⊥ _∨_
identity = identityˡ , identityʳ


-- The dual construction is a bounded meet semilattice.

dualIsBoundedMeetSemilattice : IsBoundedMeetSemilattice _≈_ (flip _≤_) _∨_ ⊥
dualIsBoundedMeetSemilattice = record
  { isMeetSemilattice = record
    { isPartialOrder  = ≥-isPartialOrder
    ; infimum         = supremum
    }
  ; maximum           = minimum
  }

dualBoundedMeetSemilattice : BoundedMeetSemilattice c ℓ₁ ℓ₂
dualBoundedMeetSemilattice = record
  { ⊤                        = ⊥
  ; isBoundedMeetSemilattice = dualIsBoundedMeetSemilattice
  }
