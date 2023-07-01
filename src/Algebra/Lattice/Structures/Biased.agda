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

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Core
open import Algebra.Consequences.Setoid
open import Data.Product.Base using (proj₁; proj₂)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module Algebra.Lattice.Structures.Biased
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Definitions _≈_
open import Algebra.Lattice.Structures _≈_

private
  variable
    ∧ ∨ : Op₂ A
    ¬   : Op₁ A
    ⊤ ⊥ : A

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

  module ML = IsMeetSemilattice isMeetSemilattice
  module JL = IsJoinSemilattice isJoinSemilattice

  isLattice₂ : IsLattice ∨ ∧
  isLattice₂ = record
    { isEquivalence = ML.isEquivalence
    ; ∨-comm        = JL.comm
    ; ∨-assoc       = JL.assoc
    ; ∨-cong        = JL.∨-cong
    ; ∧-comm        = ML.comm
    ; ∧-assoc       = ML.assoc
    ; ∧-cong        = ML.∧-cong
    ; absorptive    = absorptive
    }

open IsLattice₂ public using (isLattice₂)

------------------------------------------------------------------------
-- DistributiveLattice

-- A version of distributive lattice that is biased towards the (r)ight
-- distributivity law for (j)oin and (m)eet.
record IsDistributiveLatticeʳʲᵐ (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isLattice    : IsLattice ∨ ∧
    ∨-distribʳ-∧ : ∨ DistributesOverʳ ∧

  open IsLattice isLattice public

  setoid : Setoid a ℓ
  setoid = record { isEquivalence = isEquivalence }

  ∨-distrib-∧  = comm+distrʳ⇒distr setoid ∧-cong ∨-comm ∨-distribʳ-∧
  ∧-distribˡ-∨ = distrib+absorbs⇒distribˡ setoid ∧-cong ∧-assoc ∨-comm ∧-absorbs-∨ ∨-absorbs-∧ ∨-distrib-∧
  ∧-distrib-∨  = comm+distrˡ⇒distr setoid ∨-cong ∧-comm ∧-distribˡ-∨

  isDistributiveLatticeʳʲᵐ : IsDistributiveLattice ∨ ∧
  isDistributiveLatticeʳʲᵐ = record
    { isLattice   = isLattice
    ; ∨-distrib-∧ = ∨-distrib-∧
    ; ∧-distrib-∨ = ∧-distrib-∨
    }

open IsDistributiveLatticeʳʲᵐ public using (isDistributiveLatticeʳʲᵐ)

------------------------------------------------------------------------
-- BooleanAlgebra

-- A (r)ight biased version of a boolean algebra.
record IsBooleanAlgebraʳ
         (∨ ∧ : Op₂ A) (¬ : Op₁ A) (⊤ ⊥ : A) : Set (a ⊔ ℓ) where
  field
    isDistributiveLattice : IsDistributiveLattice ∨ ∧
    ∨-complementʳ         : RightInverse ⊤ ¬ ∨
    ∧-complementʳ         : RightInverse ⊥ ¬ ∧
    ¬-cong                : Congruent₁ ¬

  open IsDistributiveLattice isDistributiveLattice public

  setoid : Setoid a ℓ
  setoid = record { isEquivalence = isEquivalence }

  isBooleanAlgebraʳ : IsBooleanAlgebra  ∨ ∧ ¬ ⊤ ⊥
  isBooleanAlgebraʳ = record
    { isDistributiveLattice = isDistributiveLattice
    ; ∨-complement          = comm+invʳ⇒inv setoid ∨-comm ∨-complementʳ
    ; ∧-complement          = comm+invʳ⇒inv setoid ∧-comm ∧-complementʳ
    ; ¬-cong                = ¬-cong
    }

open IsBooleanAlgebraʳ public using (isBooleanAlgebraʳ)
