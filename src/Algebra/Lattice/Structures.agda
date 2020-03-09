------------------------------------------------------------------------
-- The Agda standard library
--
-- Some lattice-like structures defined by properties of _∧_ and _∨_
-- (not packed up with sets, operations, etc.)
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Lattice`,
-- unless you want to parameterise it via the equality relation.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module Algebra.Lattice.Structures
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  where

open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_

------------------------------------------------------------------------
-- Structures with 1 binary operation

record IsSemilattice (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isBand : IsBand ∙
    comm   : Commutative ∙

  open IsBand isBand public
    renaming
    ( ∙-cong  to ∧-cong
    ; ∙-congˡ to ∧-congˡ
    ; ∙-congʳ to ∧-congʳ
    )


-- Used to bring names appropriate for a meet semilattice into scope.
module IsMeetSemilattice {∧} (L : IsSemilattice ∧) where
  open IsSemilattice L public
    renaming
    ( ∧-cong  to ∧-cong
    ; ∧-congˡ to ∧-congˡ
    ; ∧-congʳ to ∧-congʳ
    )


-- Used to bring names appropriate for a join semilattice into scope.
module IsJoinSemilattice {∨} (L : IsSemilattice ∨) where
  open IsSemilattice L public
    renaming
    ( ∧-cong  to ∨-cong
    ; ∧-congˡ to ∨-congˡ
    ; ∧-congʳ to ∨-congʳ
    )

------------------------------------------------------------------------
-- Structures with 1 binary operation & 1 element

IsBoundedSemilattice = IsIdempotentCommutativeMonoid
module IsBoundedSemilattice {∙ ε} (L : IsBoundedSemilattice ∙ ε) where

  open IsIdempotentCommutativeMonoid L public

  isSemilattice : IsSemilattice ∙
  isSemilattice = record
    { isBand = isBand
    ; comm   = comm
    }


-- Used to bring names appropriate for a meet semilattice into scope.
module IsBoundedMeetSemilattice
  {∧ ⊤} (isBoundedSemilattice : IsBoundedSemilattice ∧ ⊤)
  where

  private module M = IsBoundedSemilattice isBoundedSemilattice

  open M using (isSemilattice)
  open M public using (identity; identityˡ; identityʳ)

  open IsMeetSemilattice isSemilattice public


-- Used to bring names appropriate for a join semilattice into scope.
module IsBoundedJoinSemilattice
  {∧ ⊤} (isBoundedSemilattice : IsBoundedSemilattice ∧ ⊤)
  where

  private module M = IsBoundedSemilattice isBoundedSemilattice

  open M using (isSemilattice)
  open M public using (identity; identityˡ; identityʳ)

  open IsJoinSemilattice isSemilattice public


------------------------------------------------------------------------
-- Structures with 2 binary operations

record IsLattice (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isJoinSemilattice : IsSemilattice ∨
    isMeetSemilattice : IsSemilattice ∧

  open IsJoinSemilattice isJoinSemilattice public
  open IsMeetSemilattice isMeetSemilattice public
    hiding
    ( isPartialEquivalence; isEquivalence; setoid
    ; refl; reflexive; sym; trans; ∧-congʳ; ∧-congˡ
    )


record IsDistributiveLattice (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isLattice   : IsLattice ∨ ∧
    ∨-distrib-∧ : ∨ DistributesOver ∧
    ∧-distrib-∨ : ∧ DistributesOver ∨

  open IsLattice isLattice public


------------------------------------------------------------------------
-- Structures with 2 binary ops, 1 unary op and 2 elements.

record IsBooleanAlgebra
         (∨ ∧ : Op₂ A) (¬ : Op₁ A) (⊤ ⊥ : A) : Set (a ⊔ ℓ) where
  field
    isDistributiveLattice : IsDistributiveLattice ∨ ∧
    ∨-complement          : Inverse ⊤ ¬ ∨
    ∧-complement          : Inverse ⊥ ¬ ∧
    ¬-cong                : Congruent₁ ¬

  open IsDistributiveLattice isDistributiveLattice public
