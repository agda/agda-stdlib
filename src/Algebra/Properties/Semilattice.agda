------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.Semilattice {c ℓ} (L : Semilattice c ℓ) where

open Semilattice L

open import Algebra.Structures
open import Function
open import Data.Product
open import Relation.Binary
open import Relation.Binary.Reasoning.Setoid setoid
import Relation.Binary.Construct.NaturalOrder.Left _≈_ _∧_ as LeftNaturalOrder
open import Relation.Binary.Lattice
import Relation.Binary.Properties.Poset as PosetProperties
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Every semilattice can be turned into a poset via the left natural
-- order.

poset : Poset c ℓ ℓ
poset = LeftNaturalOrder.poset isSemilattice

open Poset poset using (_≤_; isPartialOrder)
open PosetProperties poset using (_≥_; ≥-isPartialOrder)

------------------------------------------------------------------------
-- Every algebraic semilattice can be turned into an order-theoretic one.

∧-isOrderTheoreticMeetSemilattice : IsMeetSemilattice _≈_ _≤_ _∧_
∧-isOrderTheoreticMeetSemilattice = record
  { isPartialOrder = isPartialOrder
  ; infimum        = LeftNaturalOrder.infimum isSemilattice
  }

∧-isOrderTheoreticJoinSemilattice : IsJoinSemilattice _≈_ _≥_ _∧_
∧-isOrderTheoreticJoinSemilattice = record
  { isPartialOrder = ≥-isPartialOrder
  ; supremum       = IsMeetSemilattice.infimum
                       ∧-isOrderTheoreticMeetSemilattice
  }

∧-orderTheoreticMeetSemilattice : MeetSemilattice c ℓ ℓ
∧-orderTheoreticMeetSemilattice = record
  { isMeetSemilattice = ∧-isOrderTheoreticMeetSemilattice
  }

∧-orderTheoreticJoinSemilattice : JoinSemilattice c ℓ ℓ
∧-orderTheoreticJoinSemilattice = record
  { isJoinSemilattice = ∧-isOrderTheoreticJoinSemilattice
  }


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

isOrderTheoreticMeetSemilattice = ∧-isOrderTheoreticMeetSemilattice
{-# WARNING_ON_USAGE isOrderTheoreticMeetSemilattice
"Warning: isOrderTheoreticMeetSemilattice was deprecated in v1.1.
Please use ∧-isOrderTheoreticMeetSemilattice instead."
#-}
isOrderTheoreticJoinSemilattice = ∧-isOrderTheoreticJoinSemilattice
{-# WARNING_ON_USAGE isOrderTheoreticJoinSemilattice
"Warning: isOrderTheoreticJoinSemilattice was deprecated in v1.1.
Please use ∧-isOrderTheoreticJoinSemilattice instead."
#-}
orderTheoreticMeetSemilattice = ∧-orderTheoreticMeetSemilattice
{-# WARNING_ON_USAGE orderTheoreticMeetSemilattice
"Warning: orderTheoreticMeetSemilattice was deprecated in v1.1.
Please use ∧-orderTheoreticMeetSemilattice instead."
#-}
orderTheoreticJoinSemilattice = ∧-orderTheoreticJoinSemilattice
{-# WARNING_ON_USAGE orderTheoreticJoinSemilattice
"Warning: orderTheoreticJoinSemilattice was deprecated in v1.1.
Please use ∧-orderTheoreticJoinSemilattice instead."
#-}
