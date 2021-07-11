------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED. Please use
-- `Algebra.Lattice.Properties.DistributiveLattice` instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Lattice.Bundles

module Algebra.Properties.DistributiveLattice
  {ℓ₁ ℓ₂} (DL : DistributiveLattice ℓ₁ ℓ₂)
  where

open import Algebra.Lattice.Properties.DistributiveLattice DL public

{-# WARNING_ON_IMPORT
"Algebra.Properties.DistributiveLattice was deprecated in v2.0.
Use Algebra.Lattice.Properties.DistributiveLattice instead."
#-}

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

∨-∧-distribˡ = ∨-distribˡ-∧
{-# WARNING_ON_USAGE ∨-∧-distribˡ
"Warning: ∨-∧-distribˡ was deprecated in v1.1.
Please use ∨-distribˡ-∧ instead."
#-}
∨-∧-distrib = ∨-distrib-∧
{-# WARNING_ON_USAGE ∨-∧-distrib
"Warning: ∨-∧-distrib was deprecated in v1.1.
Please use ∨-distrib-∧ instead."
#-}
∧-∨-distribˡ = ∧-distribˡ-∨
{-# WARNING_ON_USAGE ∧-∨-distribˡ
"Warning: ∧-∨-distribˡ was deprecated in v1.1.
Please use ∧-distribˡ-∨ instead."
#-}
∧-∨-distribʳ = ∧-distribʳ-∨
{-# WARNING_ON_USAGE ∧-∨-distribʳ
"Warning: ∧-∨-distribʳ was deprecated in v1.1.
Please use ∧-distribʳ-∨ instead."
#-}
∧-∨-distrib = ∧-distrib-∨
{-# WARNING_ON_USAGE ∧-∨-distrib
"Warning: ∧-∨-distrib was deprecated in v1.1.
Please use ∧-distrib-∨ instead."
#-}

-- Version 1.4

replace-equality : {_≈′_ : Rel Carrier dl₂} →
                   (∀ {x y} → x ≈ y ⇔ (x ≈′ y)) →
                   DistributiveLattice _ _
replace-equality {_≈′_} ≈⇔≈′ = record
  { isDistributiveLattice = record
    { isLattice    = Lattice.isLattice
                       (LatticeProperties.replace-equality lattice ≈⇔≈′)
    ; ∨-distribʳ-∧ = λ x y z → to ⟨$⟩ ∨-distribʳ-∧ x y z
    }
  } where open module E {x y} = Equivalence (≈⇔≈′ {x} {y})
{-# WARNING_ON_USAGE replace-equality
"Warning: replace-equality was deprecated in v1.4.
Please use isDistributiveLattice from `Algebra.Construct.Subst.Equality` instead."
#-}
