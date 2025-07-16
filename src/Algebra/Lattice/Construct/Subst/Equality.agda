------------------------------------------------------------------------
-- The Agda standard library
--
-- Substituting equalities for binary relations
------------------------------------------------------------------------

-- For more general transformations between algebraic lattice structures
-- see `Algebra.Lattice.Morphisms`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Product.Base using (_,_)
open import Relation.Binary.Core using (Rel ; _⇔_)

module Algebra.Lattice.Construct.Subst.Equality
  {a ℓ₁ ℓ₂} {A : Set a} {≈₁ : Rel A ℓ₁} {≈₂ : Rel A ℓ₂}
  (equiv@(to , from) : ≈₁ ⇔ ≈₂)
  where

open import Algebra.Core using (Op₂)
open import Algebra.Lattice.Structures
  using (IsSemilattice ;IsLattice ;IsDistributiveLattice ;IsBooleanAlgebra )
open import Function.Base using (id)
open import Algebra.Construct.Subst.Equality equiv
open import Relation.Binary.Construct.Subst.Equality equiv

private
  variable
    ∧ ∨ : Op₂ A

------------------------------------------------------------------------
-- Structures

isSemilattice : IsSemilattice ≈₁ ∧ → IsSemilattice ≈₂ ∧
isSemilattice S = record
  { isBand = isBand S.isBand
  ; comm   = comm S.comm
  } where module S = IsSemilattice ≈₁ S

isLattice : IsLattice ≈₁ ∨ ∧ → IsLattice ≈₂ ∨ ∧
isLattice {∨} {∧} S = record
  { isEquivalence = isEquivalence S.isEquivalence
  ; ∨-comm        = comm      S.∨-comm
  ; ∨-assoc       = assoc {∨} S.∨-assoc
  ; ∨-cong        = cong₂     S.∨-cong
  ; ∧-comm        = comm      S.∧-comm
  ; ∧-assoc       = assoc {∧} S.∧-assoc
  ; ∧-cong        = cong₂     S.∧-cong
  ; absorptive    = absorptive {∨} {∧} S.absorptive
  } where module S = IsLattice S

isDistributiveLattice : IsDistributiveLattice ≈₁ ∨ ∧ →
                        IsDistributiveLattice ≈₂ ∨ ∧
isDistributiveLattice {∨} {∧} S = record
  { isLattice    = isLattice S.isLattice
  ; ∨-distrib-∧  = distrib {∨} {∧} S.∨-distrib-∧
  ; ∧-distrib-∨  = distrib {∧} {∨} S.∧-distrib-∨
  } where module S = IsDistributiveLattice S

isBooleanAlgebra : ∀ {¬ ⊤ ⊥} →
                   IsBooleanAlgebra ≈₁ ∨ ∧ ¬ ⊤ ⊥ →
                   IsBooleanAlgebra ≈₂ ∨ ∧ ¬ ⊤ ⊥
isBooleanAlgebra {∨} {∧} S = record
  { isDistributiveLattice = isDistributiveLattice S.isDistributiveLattice
  ; ∨-complement          = inverse {_} {∨} S.∨-complement
  ; ∧-complement          = inverse {_} {∧} S.∧-complement
  ; ¬-cong                = cong₁ S.¬-cong
  } where module S = IsBooleanAlgebra S
