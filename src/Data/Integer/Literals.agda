------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Integer.Literals where

open import Agda.Builtin.FromNat using (Number)
open import Agda.Builtin.FromNeg using (Negative)
open import Data.Unit.Base using (⊤)
open import Data.Integer.Base using (ℤ; -_; +_)

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
