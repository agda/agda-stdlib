------------------------------------------------------------------------
-- The Agda standard library
--
-- String Literals
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.String.Literals where

open import Agda.Builtin.FromString
open import Data.Unit
open import Agda.Builtin.String

isString : IsString String
isString = record
  { Constraint = λ _ → ⊤
  ; fromString = λ s → s
  }
