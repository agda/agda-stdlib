------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite sets
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin where

open import Relation.Nullary.Decidable.Core
open import Data.Nat.Base using (suc)
import Data.Nat.Properties as ℕₚ

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Fin.Base public

------------------------------------------------------------------------
-- Publicly re-export queries

open import Data.Fin.Properties public
  using (_≟_; _≤?_; _<?_)

-- # m = "m".

infix 10 #_

#_ : ∀ m {n} {m<n : True (suc m ℕₚ.≤? n)} → Fin n
#_ _ {m<n = m<n} = fromℕ≤ (toWitness m<n)
