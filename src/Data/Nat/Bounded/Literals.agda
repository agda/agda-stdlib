------------------------------------------------------------------------
-- The Agda standard library
--
-- ℕ< Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Bounded.Literals where

open import Agda.Builtin.FromNat
open import Data.Nat.Bounded using (ℕ<; module Literals)

number : ∀ n → Number (ℕ< n)
number n = record { Literals n }
