------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the `Reflects` construct
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Reflects where

open import Agda.Builtin.Equality
open import Data.Bool.Base
open import Data.Empty
open import Level
open import Relation.Nullary

private
  variable
    p : Level
    P : Set p

------------------------------------------------------------------------
-- `Reflects P b` is equivalent to `if b then P else ¬ P`.

-- These lemmas are intended to be used mostly when `b` is a value, so
-- that the `if` expressions have already been evaluated away.
-- In this case, `of` works like the relevant constructor (`ofⁿ` or
-- `ofʸ`), and `invert` strips off the constructor to just give either
-- the proof of `P` or the proof of `¬ P`.

of : ∀ {b} → if b then P else ¬ P → Reflects P b
of {b = false} ¬p = ofⁿ ¬p
of {b = true }  p = ofʸ p

invert : ∀ {b} → Reflects P b → if b then P else ¬ P
invert (ofʸ  p) = p
invert (ofⁿ ¬p) = ¬p

------------------------------------------------------------------------
-- Other lemmas

-- `Reflects` is deterministic.
det : ∀ {b b′} → Reflects P b → Reflects P b′ → b ≡ b′
det (ofʸ  p) (ofʸ  p′) = refl
det (ofʸ  p) (ofⁿ ¬p′) = ⊥-elim (¬p′ p)
det (ofⁿ ¬p) (ofʸ  p′) = ⊥-elim (¬p p′)
det (ofⁿ ¬p) (ofⁿ ¬p′) = refl
