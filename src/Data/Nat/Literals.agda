------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Literals where

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit.Base using (⊤)

number : Number Nat
number = record
  { Constraint = λ _ → ⊤
  ; fromNat    = λ n → n
  }
