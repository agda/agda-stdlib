------------------------------------------------------------------------
-- The Agda standard library
--
-- List Literals
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.List.Literals where

open import Agda.Builtin.FromString
open import Data.Unit
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Data.String.Base using (toList)

isString : IsString (List Char)
isString = record
  { Constraint = λ _ → ⊤
  ; fromString = λ s → toList s
  }
