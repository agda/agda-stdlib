------------------------------------------------------------------------
-- The Agda standard library
--
-- Fin Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Literals where

open import Agda.Builtin.FromNat
open import Data.Nat using (_<?_)
open import Data.Fin using (Fin ; #_)
open import Relation.Nullary.Decidable.Core using (True)

number : ∀ n → Number (Fin n)
number n = record
  { Constraint = λ m → True (m <? n)
  ; fromNat    = λ m {{pr}} → (# m) {n} {pr}
  }
