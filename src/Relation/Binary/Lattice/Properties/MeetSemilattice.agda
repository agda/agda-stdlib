------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by meet semilattices
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Lattice

module Relation.Binary.Lattice.Properties.MeetSemilattice
  {c ℓ₁ ℓ₂} (M : MeetSemilattice c ℓ₁ ℓ₂) where

open MeetSemilattice M

open import Algebra.Definitions _≈_
open import Data.Product
open import Function.Base using (flip)
open import Relation.Binary
open import Relation.Binary.Properties.Poset poset
import Relation.Binary.Lattice.Properties.JoinSemilattice as J

-- The dual construction is a join semilattice.

dualIsJoinSemilattice : IsJoinSemilattice _≈_ (flip _≤_) _∧_
dualIsJoinSemilattice = record
  { isPartialOrder = ≥-isPartialOrder
  ; supremum       = infimum
  }

dualJoinSemilattice : JoinSemilattice c ℓ₁ ℓ₂
dualJoinSemilattice = record
  { _∨_               = _∧_
  ; isJoinSemilattice = dualIsJoinSemilattice
  }

open J dualJoinSemilattice public
  using (isAlgSemilattice; algSemilattice; isPosemigroup; posemigroup)
  renaming
    ( ∨-monotonic  to ∧-monotonic
    ; ∨-cong       to ∧-cong
    ; ∨-comm       to ∧-comm
    ; ∨-assoc      to ∧-assoc
    ; ∨-idempotent to ∧-idempotent
    ; x≤y⇒x∨y≈y    to y≤x⇒x∧y≈y
    ; ≈-dec⇒≤-dec  to ≈-dec⇒≥-dec
    )

-- If ≈ is decidable then so is ≤

≈-dec⇒≤-dec : Decidable _≈_ → Decidable _≤_
≈-dec⇒≤-dec _≟_ = flip (≈-dec⇒≥-dec _≟_)

≈-dec⇒isDecPartialOrder : Decidable _≈_ → IsDecPartialOrder _≈_ _≤_
≈-dec⇒isDecPartialOrder _≟_ = record
  { isPartialOrder = isPartialOrder
  ; _≟_            = _≟_
  ; _≤?_           = ≈-dec⇒≤-dec _≟_
  }
