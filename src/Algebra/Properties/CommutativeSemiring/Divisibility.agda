------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic items and theory for Semiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (CommutativeSemiring)
import Algebra.Properties.Semiring.Divisibility as SemiringDiv
open import Data.Product using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

module Algebra.Properties.CommutativeSemiring.Divisibility
  {a ℓ} (R : CommutativeSemiring a ℓ) where

open CommutativeSemiring R

------------------------------------------------------------------------------
-- Re-exporting divisibility over semirings

open SemiringDiv semiring public

------------------------------------------------------------------------------
-- GCD

module _ {x y} (struc : GCD x y) where
  open GCD struc

  quot₁∣x : quot₁ ∣ x
  quot₁∣x = value , trans (*-comm value quot₁) quot₁*value≈x

  quot₂∣y : quot₂ ∣ y
  quot₂∣y = value , trans (*-comm value quot₂) quot₂*value≈y
