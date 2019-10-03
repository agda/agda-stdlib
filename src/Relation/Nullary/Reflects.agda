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

------------------------------------------------------------------------
-- `Reflects P b` is equivalent to `if b then P else ¬ P`.

of : ∀ {b} → if b then P else ¬ P → Reflects P b
of {b = false} ¬p = ofⁿ ¬p
of {b = true }  p = ofʸ p

invert : ∀ {b} → Reflects P b → if b then P else ¬ P
invert (ofʸ  p) = p
invert (ofⁿ ¬p) = ¬p
