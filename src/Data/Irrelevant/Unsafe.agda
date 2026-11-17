------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe properties of the proof irrelevance modality
------------------------------------------------------------------------

{-# OPTIONS --without-K --irrelevant-projections #-}

module Data.Irrelevant.Unsafe where

open import Data.Irrelevant hiding (_>>=_)
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b


------------------------------------------------------------------------
-- Irrelevant types are Recomputable

open import Relation.Nullary.Recomputable.Unsafe public
  using () renaming (irrelevant-recompute to recompute)

------------------------------------------------------------------------
-- Algebraic structure: Monadic bind and join

join : Irrelevant (Irrelevant A) → Irrelevant A
join = recompute $⁺_

infixl 1 _>>=_
_>>=_ : Irrelevant A → (A → Irrelevant B) → Irrelevant B
[ a ] >>= f = recompute (f a)
