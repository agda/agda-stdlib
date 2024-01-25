------------------------------------------------------------------------
-- The Agda standard library
--
-- ℤmod n Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; NonTrivial)

module Data.Integer.Modulo.Literals (n : ℕ) .{{_ : NonTrivial n}} where

open import Agda.Builtin.FromNat using (Number)
open import Data.Integer.Modulo using (ℤmod; module Literals)

number : Number (ℤmod n)
number = record { Literals n }
