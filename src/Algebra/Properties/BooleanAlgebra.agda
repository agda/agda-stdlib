------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated names
{-# OPTIONS --warning=noUserWarning #-}

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
open import Function.Bundles using (module Equivalence; _⇔_)
open import Data.Product.Base using (_,_)
