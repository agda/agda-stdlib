------------------------------------------------------------------------
-- The Agda standard library
--
-- Recomputable types and their algebra as Harrop formulas
------------------------------------------------------------------------

{-# OPTIONS --without-K --irrelevant-projections #-}

module Relation.Nullary.Recomputable.Unsafe where

open import Data.Irrelevant using (Irrelevant; irrelevant; [_])
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Re-export

open import Relation.Nullary.Recomputable public

------------------------------------------------------------------------
-- Constructions

-- Irrelevant types are Recomputable

irrelevant-recompute : Recomputable (Irrelevant A)
irrelevant (irrelevant-recompute a) = irrelevant a
