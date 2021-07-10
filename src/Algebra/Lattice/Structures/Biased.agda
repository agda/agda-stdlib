------------------------------------------------------------------------
-- The Agda standard library
--
-- Some biased records for lattice-like structures. Such records are
-- often easier to construct, but are suboptimal to use more widely and
-- should be converted to the standard record definitions immediately
-- using the provided conversion functions.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Lattice`,
-- unless you want to parameterise it via the equality relation.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Data.Product using (proj₁; proj₂)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module Algebra.Lattice.Structures.Biased
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Definitions _≈_
open import Algebra.Lattice.Structures _≈_

------------------------------------------------------------------------
-- Lattice

-- An alternative form of `IsLattice` defined in terms of
-- `IsJoinSemilattice` and `IsMeetLattice`. This form may be desirable
-- to use when constructing a lattice object as it requires fewer
-- arguments, but is often a mistake to use as an argument as it
-- contains two, *potentially different*, proofs that the equality
-- relation _≈_ is an equivalence.

record IsLattice₂ (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isJoinSemilattice : IsJoinSemilattice ∨
    isMeetSemilattice : IsMeetSemilattice ∧
    absorptive        : Absorptive ∨ ∧

isLattice₂ : ∀ {∨ ∧} → IsLattice₂ ∨ ∧ → IsLattice ∨ ∧
isLattice₂ L = record
  { isEquivalence = ML.isEquivalence
  ; ∨-comm        = JL.comm
  ; ∨-assoc       = JL.assoc
  ; ∨-cong        = JL.∨-cong
  ; ∧-comm        = ML.comm
  ; ∧-assoc       = ML.assoc
  ; ∧-cong        = ML.∧-cong
  ; absorptive    = absorptive
  }
  where
    open IsLattice₂ L
    module ML = IsMeetSemilattice isMeetSemilattice
    module JL = IsJoinSemilattice isJoinSemilattice
