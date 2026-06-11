------------------------------------------------------------------------
-- The Agda standard library
--
-- Recomputable types and their algebra as Harrop formulas
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --irrelevant-projections #-}

module Relation.Nullary.Recomputable.Unsafe where

open import Data.Empty using (⊥)
open import Data.Irrelevant using (Irrelevant; irrelevant; [_])
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Level using (Level)
open import Relation.Nullary.Negation.Core using (¬_)

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

