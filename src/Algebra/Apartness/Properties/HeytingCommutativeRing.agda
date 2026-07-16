------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Heyting Commutative Rings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Apartness.Bundles using (HeytingCommutativeRing)

module Algebra.Apartness.Properties.HeytingCommutativeRing
  {c ℓ₁ ℓ₂} (heytingCommutativeRing : HeytingCommutativeRing c ℓ₁ ℓ₂) where

open import Algebra.Bundles using (CommutativeRing)

open HeytingCommutativeRing heytingCommutativeRing using (commutativeRing)
open CommutativeRing commutativeRing using (ring)
open import Algebra.Properties.Ring ring using (x-0#≈x)


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 3.0

x-0≈x = x-0#≈x
{-# WARNING_ON_USAGE x-0≈x
"Warning: x-0≈x was deprecated in v3.0.
Please use Algebra.Properties.Ring.x-0#≈x instead."
#-}

open HeytingCommutativeRing heytingCommutativeRing public using (#-sym)
{-# WARNING_ON_USAGE #-sym
"Warning: #-sym was deprecated in v3.0.
Please use Algebra.Apartness.Structures.IsHeytingCommutativeRing.#-sym instead."
#-}
