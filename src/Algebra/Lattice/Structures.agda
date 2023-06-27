------------------------------------------------------------------------
-- The Agda standard library
--
-- Some lattice-like structures defined by properties of _∧_ and _∨_
-- (not packed up with sets, operations, etc.)
--
-- For lattices defined via an order relation, see
-- Relation.Binary.Lattice.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Lattice`,
-- unless you want to parameterise it via the equality relation.

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Core
open import Data.Product.Base using (proj₁; proj₂)
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
IsMeetSemilattice = IsSemilattice
module IsMeetSemilattice {∧} (L : IsMeetSemilattice ∧) where
  open IsSemilattice L public
    renaming
    ( ∧-cong  to ∧-cong
    ; ∧-congˡ to ∧-congˡ
    ; ∧-congʳ to ∧-congʳ
    )

-- Used to bring names appropriate for a join semilattice into scope.
IsJoinSemilattice = IsSemilattice
module IsJoinSemilattice {∨} (L : IsJoinSemilattice ∨) where
  open IsSemilattice L public
    renaming
    ( ∧-cong  to ∨-cong
    ; ∧-congˡ to ∨-congˡ
    ; ∧-congʳ to ∨-congʳ
    )

------------------------------------------------------------------------
-- Structures with 1 binary operation & 1 element

-- A bounded semi-lattice is the same thing as an idempotent commutative
-- monoid.
IsBoundedSemilattice = IsIdempotentCommutativeMonoid
module IsBoundedSemilattice {∙ ε} (L : IsBoundedSemilattice ∙ ε) where

  open IsIdempotentCommutativeMonoid L public

  isSemilattice : IsSemilattice ∙
  isSemilattice = record
    { isBand = isBand
    ; comm   = comm
    }


-- Used to bring names appropriate for a bounded meet semilattice
-- into scope.
IsBoundedMeetSemilattice = IsBoundedSemilattice
module IsBoundedMeetSemilattice {∧ ⊤} (L : IsBoundedMeetSemilattice ∧ ⊤)
  where

  open IsBoundedSemilattice L public
    using (identity; identityˡ; identityʳ)
    renaming (isSemilattice to isMeetSemilattice)

  open IsMeetSemilattice isMeetSemilattice public


-- Used to bring names appropriate for a bounded join semilattice
-- into scope.
IsBoundedJoinSemilattice = IsBoundedSemilattice
module IsBoundedJoinSemilattice {∨ ⊥} (L : IsBoundedJoinSemilattice ∨ ⊥)
  where

  open IsBoundedSemilattice L public
    using (identity; identityˡ; identityʳ)
    renaming (isSemilattice to isJoinSemilattice)

  open IsJoinSemilattice isJoinSemilattice public

------------------------------------------------------------------------
-- Structures with 2 binary operations

-- Note that `IsLattice` is not defined in terms of `IsMeetSemilattice`
-- and `IsJoinSemilattice` for two reasons:
--   1) it would result in a structure with two *different* proofs that
--   the equality relation `≈` is an equivalence relation.
--   2) the idempotence laws of ∨ and ∧ can be derived from the
--   absorption laws, which makes the corresponding "idem" fields
--   redundant.
--
-- It is possible to construct the `IsLattice` record from
-- `IsMeetSemilattice` and `IsJoinSemilattice` via the `IsLattice₂`
-- record found in `Algebra.Lattice.Structures.Biased`.
--
-- The derived idempotence laws are stated and proved in
-- `Algebra.Lattice.Properties.Lattice` along with the fact that every
-- lattice consists of two semilattices.

record IsLattice (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_
    ∨-comm        : Commutative ∨
    ∨-assoc       : Associative ∨
    ∨-cong        : Congruent₂ ∨
    ∧-comm        : Commutative ∧
    ∧-assoc       : Associative ∧
    ∧-cong        : Congruent₂ ∧
    absorptive    : Absorptive ∨ ∧

  open IsEquivalence isEquivalence public

  ∨-absorbs-∧ : ∨ Absorbs ∧
  ∨-absorbs-∧ = proj₁ absorptive

  ∧-absorbs-∨ : ∧ Absorbs ∨
  ∧-absorbs-∨ = proj₂ absorptive

  ∧-congˡ : LeftCongruent ∧
  ∧-congˡ y≈z = ∧-cong refl y≈z

  ∧-congʳ : RightCongruent ∧
  ∧-congʳ y≈z = ∧-cong y≈z refl

  ∨-congˡ : LeftCongruent ∨
  ∨-congˡ y≈z = ∨-cong refl y≈z

  ∨-congʳ : RightCongruent ∨
  ∨-congʳ y≈z = ∨-cong y≈z refl


record IsDistributiveLattice (∨ ∧ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isLattice   : IsLattice ∨ ∧
    ∨-distrib-∧ : ∨ DistributesOver ∧
    ∧-distrib-∨ : ∧ DistributesOver ∨

  open IsLattice isLattice public

  ∨-distribˡ-∧ : ∨ DistributesOverˡ ∧
  ∨-distribˡ-∧ = proj₁ ∨-distrib-∧

  ∨-distribʳ-∧ : ∨ DistributesOverʳ ∧
  ∨-distribʳ-∧ = proj₂ ∨-distrib-∧

  ∧-distribˡ-∨ : ∧ DistributesOverˡ ∨
  ∧-distribˡ-∨ = proj₁ ∧-distrib-∨

  ∧-distribʳ-∨ : ∧ DistributesOverʳ ∨
  ∧-distribʳ-∨ = proj₂ ∧-distrib-∨

------------------------------------------------------------------------
-- Structures with 2 binary ops, 1 unary op and 2 elements.

record IsBooleanAlgebra (∨ ∧ : Op₂ A) (¬ : Op₁ A) (⊤ ⊥ : A) : Set (a ⊔ ℓ)
  where

  field
    isDistributiveLattice : IsDistributiveLattice ∨ ∧
    ∨-complement          : Inverse ⊤ ¬ ∨
    ∧-complement          : Inverse ⊥ ¬ ∧
    ¬-cong                : Congruent₁ ¬

  open IsDistributiveLattice isDistributiveLattice public

  ∨-complementˡ : LeftInverse ⊤ ¬ ∨
  ∨-complementˡ = proj₁ ∨-complement

  ∨-complementʳ : RightInverse ⊤ ¬ ∨
  ∨-complementʳ = proj₂ ∨-complement

  ∧-complementˡ : LeftInverse ⊥ ¬ ∧
  ∧-complementˡ = proj₁ ∧-complement

  ∧-complementʳ : RightInverse ⊥ ¬ ∧
  ∧-complementʳ = proj₂ ∧-complement
