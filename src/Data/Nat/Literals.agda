------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural Literals
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Nat.Literals where

open import Agda.Builtin.FromNat
open import Agda.Builtin.Nat
open import Data.Unit

number : Number Nat
number = record
  { Constraint = λ _ → ⊤
  ; fromNat    = λ n → n
  }
