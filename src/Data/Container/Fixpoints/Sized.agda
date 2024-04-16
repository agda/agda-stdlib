------------------------------------------------------------------------
-- The Agda standard library
--
-- Sized fixpoints of containers, based on the work of Abbott and others
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Data.Container.Fixpoints.Sized where

open import Level using (Level; _⊔_)
open import Size using (Size)
open import Codata.Sized.M using (M)
open import Data.W.Sized using (W)
open import Data.Container hiding (μ) public

private
  variable
    s p : Level

-- The sized least and greatest fixpoints of a container.

μ : Container s p → Size → Set (s ⊔ p)
μ = W

ν : Container s p → Size → Set (s ⊔ p)
ν = M
