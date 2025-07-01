------------------------------------------------------------------------
-- The Agda standard library
--
-- List Literals
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Literals where

open import Agda.Builtin.FromString using (IsString)
open import Data.Unit.Base using (⊤)
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.List using (List)
open import Data.String.Base using (toList)

isString : IsString (List Char)
isString = record
  { Constraint = λ _ → ⊤
  ; fromString = λ s → toList s
  }
