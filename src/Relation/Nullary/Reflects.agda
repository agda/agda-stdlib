------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the `Reflects` construct
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Reflects where

open import Data.Bool.Base
open import Level
open import Relation.Nullary

variable
  p : Level
  P : Set p

invert-true : Reflects P true → P
invert-true (true p) = p

invert-false : Reflects P false → ¬ P
invert-false (false ¬p) = ¬p

invert : ∀ {b} → Reflects P b → if b then P else ¬ P
invert (true   p) = p
invert (false ¬p) = ¬p
