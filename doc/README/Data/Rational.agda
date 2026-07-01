------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing where the rational numbers and some related
-- operations and properties are defined, and how they can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README.Data.Rational where

open import Data.Integer using (+_)
open import Data.Rational
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

1/4 : ℚ
1/4 = + 1 / 4

3/4 : ℚ
3/4 = + 3 / 4

expr : ℚ
expr = (1/4 + ½) * 1ℚ - 0ℚ

eqEx : expr ≡ 3/4
eqEx = refl

open import Data.Rational.Tactic.RingSolver

lemma : ∀ (x y : ℚ) → x + y + 1/4 + ½ ≡ 3/4 + y + x
lemma = solve-∀
