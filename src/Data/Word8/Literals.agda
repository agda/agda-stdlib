------------------------------------------------------------------------
-- The Agda standard library
--
-- Byte Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module Data.Word8.Literals where

open import Agda.Builtin.FromNat using (Number)
open import Data.Unit.Base using (⊤)
open import Data.Word8.Base using (Word8; fromℕ)

number : Number Word8
number = record
  { Constraint = λ _ → ⊤
  ; fromNat    = λ w → fromℕ w
  }
