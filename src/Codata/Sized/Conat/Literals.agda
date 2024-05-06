------------------------------------------------------------------------
-- The Agda standard library
--
-- Conat Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Codata.Sized.Conat.Literals where

open import Agda.Builtin.FromNat using (Number)
open import Data.Unit.Base using (⊤)
open import Codata.Sized.Conat using (Conat; fromℕ)

number : ∀ {i} → Number (Conat i)
number = record
  { Constraint = λ _ → ⊤
  ; fromNat    = λ n → fromℕ n
  }
