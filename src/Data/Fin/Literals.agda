------------------------------------------------------------------------
-- The Agda standard library
--
-- Fin Literals
------------------------------------------------------------------------

module Data.Fin.Literals where

open import Agda.Builtin.FromNat
open import Data.Nat.Base
open import Data.Fin using (Fin ; #_)
open import Relation.Nullary.Decidable using (True)

number : ∀ n → Number (Fin n)
number n = record
  { Constraint = λ m → True (suc m ≤? n)
  ; fromNat    = λ m {{pr}} → (# m) {n} {pr}
  }
