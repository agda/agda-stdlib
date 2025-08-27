------------------------------------------------------------------------
-- The Agda standard library
--
-- Word64 Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Word64.Literals where

open import Agda.Builtin.FromNat using (Number)
open import Data.Unit.Base using (⊤)
open import Data.Word64.Base using (Word64; fromℕ)

number : Number Word64
number = record
  { Constraint = λ _ → ⊤
  ; fromNat    = λ w → fromℕ w
  }
