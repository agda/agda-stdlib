------------------------------------------------------------------------
-- The Agda standard library
--
-- Fixed points of containers
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Data.Container.FixedPoints where

open import Level using (Level; _⊔_)
open import Codata.M using (M)
open import Data.W using (W)
open import Data.Container using (Container)
open import Size

private
  variable
    s p : Level

-- The least and greatest fixpoints of a container.

μ : Container s p → Set (s ⊔ p)
μ = W

ν : Container s p → Set (s ⊔ p)
ν C = M C ∞
