------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer Literals
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.Literals where

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Data.Unit
open import Data.Integer

number : Number ℤ
number = record
  { Constraint = λ _ → ⊤
  ; fromNat    = λ n → + n
  }

negative : Negative ℤ
negative = record
  { Constraint = λ _ → ⊤
  ; fromNeg    = λ n → - (+ n)
  }
