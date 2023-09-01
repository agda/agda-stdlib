------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

-- Disabled to prevent warnings from deprecated names
{-# OPTIONS --warn=noUserWarning #-}

open import Algebra.Lattice.Bundles

module Algebra.Properties.BooleanAlgebra
  {b₁ b₂} (B : BooleanAlgebra b₁ b₂)
  where

{-# WARNING_ON_IMPORT
"Algebra.Properties.BooleanAlgebra was deprecated in v2.0.
Use Algebra.Lattice.Properties.BooleanAlgebra instead."
#-}

open import Algebra.Lattice.Properties.BooleanAlgebra B public

open BooleanAlgebra B

import Algebra.Properties.DistributiveLattice as DistribLatticeProperties

open import Algebra.Structures _≈_
open import Relation.Binary
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (_⇔_; module Equivalence)
open import Data.Product.Base using (_,_)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.4

replace-equality : {_≈′_ : Rel Carrier b₂} →
                   (∀ {x y} → x ≈ y ⇔ (x ≈′ y)) →
                   BooleanAlgebra _ _
replace-equality {_≈′_} ≈⇔≈′ = record
  { isBooleanAlgebra = record
    { isDistributiveLattice = DistributiveLattice.isDistributiveLattice
        (DistribLatticeProperties.replace-equality distributiveLattice ≈⇔≈′)
    ; ∨-complement          = ((λ x → to ⟨$⟩ ∨-complementˡ x) , λ x → to ⟨$⟩ ∨-complementʳ x)
    ; ∧-complement          = ((λ x → to ⟨$⟩ ∧-complementˡ x) , λ x → to ⟨$⟩ ∧-complementʳ x)
    ; ¬-cong                = λ i≈j → to ⟨$⟩ ¬-cong (from ⟨$⟩ i≈j)
    }
  } where open module E {x y} = Equivalence (≈⇔≈′ {x} {y})
{-# WARNING_ON_USAGE replace-equality
"Warning: replace-equality was deprecated in v1.4.
Please use isBooleanAlgebra from `Algebra.Construct.Subst.Equality` instead."
#-}
