------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.Semilattice {l₁ l₂} (L : Semilattice l₁ l₂) where

open Semilattice L
open import Algebra.Structures
open import Relation.Binary
import Relation.Binary.Construct.NaturalOrder.Left as LeftNaturalOrder
import Relation.Binary.Lattice as R
import Relation.Binary.Properties.Poset as R
open import Relation.Binary.Reasoning.Setoid setoid
open import Function
open import Data.Product

------------------------------------------------------------------------
-- Every semilattice can be turned into a poset via the left natural
-- order.

poset : Poset _ _ _
poset = LeftNaturalOrder.poset _≈_ _∧_ isSemilattice

open Poset poset using (_≤_; isPartialOrder)

------------------------------------------------------------------------
-- Every algebraic semilattice can be turned into an order-theoretic one.

isOrderTheoreticMeetSemilattice : R.IsMeetSemilattice _≈_ _≤_ _∧_
isOrderTheoreticMeetSemilattice = record
  { isPartialOrder = isPartialOrder
  ; infimum        = LeftNaturalOrder.infimum _≈_ _∧_ isSemilattice
  }

orderTheoreticMeetSemilattice : R.MeetSemilattice _ _ _
orderTheoreticMeetSemilattice = record
  { isMeetSemilattice = isOrderTheoreticMeetSemilattice }

isOrderTheoreticJoinSemilattice : R.IsJoinSemilattice _≈_ (flip _≤_) _∧_
isOrderTheoreticJoinSemilattice = record
  { isPartialOrder = R.invIsPartialOrder poset
  ; supremum       = R.IsMeetSemilattice.infimum
                       isOrderTheoreticMeetSemilattice
  }

orderTheoreticJoinSemilattice : R.JoinSemilattice _ _ _
orderTheoreticJoinSemilattice = record
  { isJoinSemilattice = isOrderTheoreticJoinSemilattice }
