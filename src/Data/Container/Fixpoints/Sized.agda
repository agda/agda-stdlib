------------------------------------------------------------------------
-- The Agda standard library
--
-- Sized fixpoints of containers, based on the work of Abbott and others
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Data.Container.Fixpoints.Sized where

open import Level
open import Size
open import Codata.M
open import Data.W.Sized
open import Data.Container hiding (μ) public

private
  variable
    s p : Level

-- The sized least and greatest fixpoints of a container.

μ : Container s p → Size → Set (s ⊔ p)
μ = W

ν : Container s p → Size → Set (s ⊔ p)
ν = M
