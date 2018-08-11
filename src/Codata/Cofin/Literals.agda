------------------------------------------------------------------------
-- The Agda standard library
--
-- Conat Literals
------------------------------------------------------------------------

module Codata.Cofin.Literals where

open import Data.Nat
open import Agda.Builtin.FromNat
open import Codata.Conat
open import Codata.Conat.Properties
open import Codata.Cofin
open import Relation.Nullary.Decidable

number : ∀ n → Number (Cofin n)
number n = record
  { Constraint = λ k → True (suc k ℕ≤? n)
  ; fromNat    = λ n {{p}} → fromℕ< (toWitness p)
  }

