------------------------------------------------------------------------
-- The Agda standard library
--
-- Conat Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Cofin.Literals where

open import Agda.Builtin.FromNat using (Number)
open import Data.Nat.Base using (ℕ; suc)
open import Codata.Sized.Conat using (Conat)
open import Codata.Sized.Conat.Properties using (_ℕ≤?_)
open import Codata.Sized.Cofin using (Cofin; fromℕ<)
open import Relation.Nullary.Decidable using (True; toWitness)

number : ∀ n → Number (Cofin n)
number n = record
  { Constraint = λ k → True (suc k ℕ≤? n)
  ; fromNat    = λ n {{p}} → fromℕ< (toWitness p)
  }
