------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

-- Disabled to prevent warnings from deprecated names
{-# OPTIONS --warn=noUserWarning #-}

open import Algebra.Lattice.Bundles
open import Algebra.Lattice.Structures.Biased
open import Relation.Binary
open import Function.Equality
open import Function.Equivalence
import Algebra.Construct.Subst.Equality as SubstEq

module Algebra.Properties.DistributiveLattice
  {ℓ₁ ℓ₂} (DL : DistributiveLattice ℓ₁ ℓ₂)
  where

{-# WARNING_ON_IMPORT
"Algebra.Properties.DistributiveLattice was deprecated in v2.0.
Use Algebra.Lattice.Properties.DistributiveLattice instead."
#-}

open DistributiveLattice DL
open import Algebra.Lattice.Properties.DistributiveLattice DL public
import Algebra.Properties.Lattice as LatticeProperties

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.4

replace-equality : {_≈′_ : Rel Carrier ℓ₂} →
                   (∀ {x y} → x ≈ y ⇔ (x ≈′ y)) →
                   DistributiveLattice _ _
replace-equality {_≈′_} ≈⇔≈′ = record
  { isDistributiveLattice = isDistributiveLatticeʳʲᵐ (record
    { isLattice    = Lattice.isLattice
                       (LatticeProperties.replace-equality lattice ≈⇔≈′)
    ; ∨-distribʳ-∧ = λ x y z → to ⟨$⟩ ∨-distribʳ-∧ x y z
    })
  } where open module E {x y} = Equivalence (≈⇔≈′ {x} {y})
{-# WARNING_ON_USAGE replace-equality
"Warning: replace-equality was deprecated in v1.4.
Please use isDistributiveLattice from `Algebra.Construct.Subst.Equality` instead."
#-}
