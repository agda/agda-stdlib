------------------------------------------------------------------------
-- The Agda standard library
--
-- String Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.String.Literals where

open import Agda.Builtin.FromString using (IsString)
open import Data.Unit.Base using (⊤)
open import Agda.Builtin.String using (String)

isString : IsString String
isString = record
  { Constraint = λ _ → ⊤
  ; fromString = λ s → s
  }
