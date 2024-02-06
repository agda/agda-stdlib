------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite sets
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin where

open import Relation.Nullary.Decidable.Core
import Data.Nat.Properties as ℕ

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Fin.Base public

------------------------------------------------------------------------
-- Publicly re-export queries

open import Data.Fin.Properties public
  using (_≟_; _≤?_; _<?_)

-- # m = "m".

infix 10 #_

#_ : ∀ m {n} {m<n : True (m ℕ.<? n)} → Fin n
#_ _ {m<n = m<n} = fromℕ< (toWitness m<n)
