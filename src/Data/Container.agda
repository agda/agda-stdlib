------------------------------------------------------------------------
-- The Agda standard library
--
-- Containers, based on the work of Abbott and others
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container where

open import Level using (_⊔_)
open import Codata.Musical.M
open import Data.W

------------------------------------------------------------------------
-- Containers

-- A container is a set of shapes, and for every shape a set of positions.

open import Data.Container.Core public

-- The least and greatest fixpoints of a container.

μ : ∀ {s p} → Container s p → Set (s ⊔ p)
μ = W

ν : ∀ {s p} → Container s p → Set (s ⊔ p)
ν = M
