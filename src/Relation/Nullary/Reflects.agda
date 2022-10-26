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
open import Function.Base using (_$_)

open import Relation.Nullary.Negation.Core

private
  variable
    p : Level
    P : Set p

------------------------------------------------------------------------
-- `Reflects` idiom.

-- The truth value of P is reflected by a boolean value.
-- `Reflects P b` is equivalent to `if b then P else ¬ P`.

data Reflects {p} (P : Set p) : Bool → Set p where
  ofʸ : ( p :   P) → Reflects P true
  ofⁿ : (¬p : ¬ P) → Reflects P false

------------------------------------------------------------------------
-- Constructors and destructors

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
-- Interaction with negation, product, sums etc.

-- If we can decide P, then we can decide its negation.

¬-reflects : ∀ {b} → Reflects P b → Reflects (¬ P) (not b)
¬-reflects (ofʸ  p) = ofⁿ (_$ p)
¬-reflects (ofⁿ ¬p) = ofʸ ¬p

------------------------------------------------------------------------
-- Other lemmas

fromEquivalence : ∀ {b} → (T b → P) → (P → T b) → Reflects P b
fromEquivalence {b = true}  sound complete = ofʸ (sound _)
fromEquivalence {b = false} sound complete = ofⁿ complete

-- `Reflects` is deterministic.
det : ∀ {b b′} → Reflects P b → Reflects P b′ → b ≡ b′
det (ofʸ  p) (ofʸ  p′) = refl
det (ofʸ  p) (ofⁿ ¬p′) = ⊥-elim (¬p′ p)
det (ofⁿ ¬p) (ofʸ  p′) = ⊥-elim (¬p p′)
det (ofⁿ ¬p) (ofⁿ ¬p′) = refl
