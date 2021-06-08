------------------------------------------------------------------------
-- The Agda standard library
--
-- Greatest fixpoint for indexed containers - using guardedness
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Data.Container.Indexed.Fixpoints.Guarded where

open import Level using (Level; _⊔_)
open import Codata.Musical.M.Indexed using (M)
open import Data.Container.Indexed using (Container)
open import Relation.Unary using (Pred)

private
  variable
    o c r : Level
    O : Set o


-- The least fixpoint can be found in `Data.Container`

open Data.Container.Indexed public
  using (μ)

-- This lives in its own module due to its use of guardedness.

ν : Container O O c r → Pred O _
ν = M
