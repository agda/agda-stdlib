------------------------------------------------------------------------
-- The Agda standard library
--
-- Greatest fixpoint for containers
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Data.Container.GreatestFixpoint where

open import Level using (Level; _⊔_)
open import Codata.M using (M)
open import Data.Container using (Container)
open import Size

private
  variable
    s p : Level

-- This lives in its own module due to its unsafe use of sized types.
-- The least fixpoint can be found in `Data.Container`

ν : Container s p → Set (s ⊔ p)
ν C = M C ∞
