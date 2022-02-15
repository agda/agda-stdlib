------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Algebra.Lattice.Properties.Semilattice` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Lattice

module Algebra.Properties.Semilattice {c ℓ} (L : Semilattice c ℓ) where

open import Algebra.Lattice.Properties.Semilattice L public

{-# WARNING_ON_IMPORT
"Algebra.Properties.Semilattice was deprecated in v2.0.
Use Algebra.Lattice.Properties.Semilattice instead."
#-}

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
