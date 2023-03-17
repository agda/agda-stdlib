------------------------------------------------------------------------
-- The Agda standard library
--
-- Conat Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Conat.Literals where

open import Agda.Builtin.FromNat
open import Data.Unit
open import Codata.Sized.Conat

number : ∀ {i} → Number (Conat i)
number = record
  { Constraint = λ _ → ⊤
  ; fromNat    = λ n → fromℕ n
  }
