------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties of semilattices
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Lattice.Bundles using (Semilattice)
open import Relation.Binary.Bundles using (Poset)
import Relation.Binary.Lattice as B
import Relation.Binary.Properties.Poset as PosetProperties

module Algebra.Lattice.Properties.Semilattice
  {c ℓ} (L : Semilattice c ℓ) where

open Semilattice L renaming (_∙_ to _∧_)

open import Relation.Binary.Reasoning.Setoid setoid
import Relation.Binary.Construct.NaturalOrder.Left _≈_ _∧_
  as LeftNaturalOrder

------------------------------------------------------------------------
-- Every semilattice can be turned into a poset via the left natural
-- order.

poset : Poset c ℓ ℓ
poset = LeftNaturalOrder.poset isSemilattice

open Poset poset using (_≤_; isPartialOrder)
open PosetProperties poset using (_≥_; ≥-isPartialOrder)

------------------------------------------------------------------------
-- Every algebraic semilattice can be turned into an order-theoretic one.

∧-isOrderTheoreticMeetSemilattice : B.IsMeetSemilattice _≈_ _≤_ _∧_
∧-isOrderTheoreticMeetSemilattice = record
  { isPartialOrder = isPartialOrder
  ; infimum        = LeftNaturalOrder.infimum isSemilattice
  }

∧-isOrderTheoreticJoinSemilattice : B.IsJoinSemilattice _≈_ _≥_ _∧_
∧-isOrderTheoreticJoinSemilattice = record
  { isPartialOrder = ≥-isPartialOrder
  ; supremum       = B.IsMeetSemilattice.infimum
                       ∧-isOrderTheoreticMeetSemilattice
  }

∧-orderTheoreticMeetSemilattice : B.MeetSemilattice c ℓ ℓ
∧-orderTheoreticMeetSemilattice = record
  { isMeetSemilattice = ∧-isOrderTheoreticMeetSemilattice
  }

∧-orderTheoreticJoinSemilattice : B.JoinSemilattice c ℓ ℓ
∧-orderTheoreticJoinSemilattice = record
  { isJoinSemilattice = ∧-isOrderTheoreticJoinSemilattice
  }
