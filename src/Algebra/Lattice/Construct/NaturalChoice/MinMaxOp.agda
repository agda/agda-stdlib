------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of min and max operators specified over a total preorder.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Lattice.Bundles
open import Algebra.Construct.NaturalChoice.Base
open import Relation.Binary

module Algebra.Lattice.Construct.NaturalChoice.MinMaxOp
  {a ℓ₁ ℓ₂} {O : TotalPreorder a ℓ₁ ℓ₂}
  (minOp : MinOperator O)
  (maxOp : MaxOperator O)
  where

open TotalPreorder O
open MinOperator minOp
open MaxOperator maxOp

open import Algebra.Lattice.Structures _≈_
open import Algebra.Construct.NaturalChoice.MinMaxOp minOp maxOp
open import Relation.Binary.Reasoning.Preorder preorder

------------------------------------------------------------------------
-- Re-export properties of individual operators

open import Algebra.Lattice.Construct.NaturalChoice.MinOp minOp public
open import Algebra.Lattice.Construct.NaturalChoice.MaxOp maxOp public

------------------------------------------------------------------------
-- Structures

⊔-⊓-isLattice : IsLattice _⊔_ _⊓_
⊔-⊓-isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm        = ⊔-comm
  ; ∨-assoc       = ⊔-assoc
  ; ∨-cong        = ⊔-cong
  ; ∧-comm        = ⊓-comm
  ; ∧-assoc       = ⊓-assoc
  ; ∧-cong        = ⊓-cong
  ; absorptive    = ⊔-⊓-absorptive
  }

⊓-⊔-isLattice : IsLattice _⊓_ _⊔_
⊓-⊔-isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm        = ⊓-comm
  ; ∨-assoc       = ⊓-assoc
  ; ∨-cong        = ⊓-cong
  ; ∧-comm        = ⊔-comm
  ; ∧-assoc       = ⊔-assoc
  ; ∧-cong        = ⊔-cong
  ; absorptive    = ⊓-⊔-absorptive
  }

⊓-⊔-isDistributiveLattice : IsDistributiveLattice _⊓_ _⊔_
⊓-⊔-isDistributiveLattice = record
  { isLattice    = ⊓-⊔-isLattice
  ; ∨-distrib-∧  = ⊓-distrib-⊔
  ; ∧-distrib-∨  = ⊔-distrib-⊓
  }

⊔-⊓-isDistributiveLattice : IsDistributiveLattice _⊔_ _⊓_
⊔-⊓-isDistributiveLattice = record
  { isLattice    = ⊔-⊓-isLattice
  ; ∨-distrib-∧  = ⊔-distrib-⊓
  ; ∧-distrib-∨  = ⊓-distrib-⊔
  }

------------------------------------------------------------------------
-- Bundles

⊔-⊓-lattice : Lattice _ _
⊔-⊓-lattice = record
  { isLattice = ⊔-⊓-isLattice
  }

⊓-⊔-lattice : Lattice _ _
⊓-⊔-lattice = record
  { isLattice = ⊓-⊔-isLattice
  }

⊔-⊓-distributiveLattice : DistributiveLattice _ _
⊔-⊓-distributiveLattice = record
  { isDistributiveLattice = ⊔-⊓-isDistributiveLattice
  }

⊓-⊔-distributiveLattice : DistributiveLattice _ _
⊓-⊔-distributiveLattice = record
  { isDistributiveLattice = ⊓-⊔-isDistributiveLattice
  }
