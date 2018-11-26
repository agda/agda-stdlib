------------------------------------------------------------------------
-- The Agda standard library
--
-- Fin Literals
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Fin.Literals where

open import Agda.Builtin.FromNat
open import Data.Nat using (suc; _≤?_)
open import Data.Fin using (Fin ; #_)
open import Relation.Nullary.Decidable using (True)

number : ∀ n → Number (Fin n)
number n = record
  { Constraint = λ m → True (suc m ≤? n)
  ; fromNat    = λ m {{pr}} → (# m) {n} {pr}
  }
