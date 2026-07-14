------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated names
{-# OPTIONS --warning=noUserWarning #-}

open import Algebra.Lattice.Bundles
open import Algebra.Lattice.Structures.Biased
open import Relation.Binary
open import Function.Bundles using (module Equivalence; _⇔_)
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
