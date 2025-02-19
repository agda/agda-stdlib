------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Heyting Commutative Rings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Apartness.Bundles using (HeytingCommutativeRing)

module Algebra.Apartness.Properties.HeytingCommutativeRing
  {c ℓ₁ ℓ₂} (HCR : HeytingCommutativeRing c ℓ₁ ℓ₂) where

open import Algebra.Bundles using (CommutativeRing)

open HeytingCommutativeRing HCR
open CommutativeRing commutativeRing using (ring)
open import Algebra.Properties.Ring ring using (x-0#≈x)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.3

x-0≈x = x-0#≈x
{-# WARNING_ON_USAGE x-0≈x
"Warning: x-0≈x was deprecated in v2.3.
Please use Algebra.Properties.Ring.x-0#≈x instead."
#-}
