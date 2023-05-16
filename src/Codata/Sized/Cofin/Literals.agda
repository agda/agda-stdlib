------------------------------------------------------------------------
-- The Agda standard library
--
-- Conat Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Cofin.Literals where

open import Data.Nat.Base
open import Agda.Builtin.FromNat
open import Codata.Sized.Conat
open import Codata.Sized.Conat.Properties
open import Codata.Sized.Cofin
open import Relation.Nullary.Decidable

number : ∀ n → Number (Cofin n)
number n = record
  { Constraint = λ k → True (suc k ℕ≤? n)
  ; fromNat    = λ n {{p}} → fromℕ< (toWitness p)
  }
