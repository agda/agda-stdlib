------------------------------------------------------------------------
-- The Agda standard library
--
-- Fixpoints for containers - using guardedness
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Data.Container.Fixpoints.Guarded where

open import Level using (Level; _⊔_)
open import Codata.Musical.M using (M)
open import Data.Container using (Container)

private
  variable
    s p : Level

-- The least fixpoint can be found in `Data.Container`

open Data.Container public
  using (μ)

-- This lives in its own module due to its use of guardedness.

ν : Container s p → Set (s ⊔ p)
ν C = M C
