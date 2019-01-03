------------------------------------------------------------------------
-- The Agda standard library
--
-- Conat Literals
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Codata.Conat.Literals where

open import Agda.Builtin.FromNat
open import Data.Unit
open import Codata.Conat

number : ∀ {i} → Number (Conat i)
number = record
  { Constraint = λ _ → ⊤
  ; fromNat    = λ n → fromℕ n
  }
