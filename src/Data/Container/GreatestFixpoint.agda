------------------------------------------------------------------------
-- The Agda standard library
--
-- Greatest fixpoint for containers
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Data.Container.GreatestFixpoint where

open import Level using (Level; _⊔_)
open import Codata.Musical.M using (M)
open import Data.Container using (Container)

private
  variable
    s p : Level

-- This lives in its own module due to its unsafe use of sized types.
-- The least fixpoint can be found in `Data.Container`

ν : Container s p → Set (s ⊔ p)
ν C = M C
