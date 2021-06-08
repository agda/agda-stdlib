------------------------------------------------------------------------
-- The Agda standard library
--
-- Greatest fixpoint for containers
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Data.Container.Indexed.GreatestFixpoint where

open import Level using (Level; _⊔_)
open import Codata.Musical.M.Indexed
open import Data.Container.Indexed using (Container)
open import Relation.Unary using (Pred)

private
  variable
    o c r : Level
    O : Set o

-- This lives in its own module due to its use of guardedness.
-- The least fixpoint can be found in `Data.Container.Indexed`

ν : Container O O c r → Pred O _
ν = M
