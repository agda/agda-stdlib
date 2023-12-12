------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing where the rational numbers and some related
-- operations and properties are defined, and how they can be used
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module README.Data.Rational where

-- The rational numbers and various arithmetic operations are defined in
-- Data.Rational.

open import Data.Integer using (+_)
open import Data.Rational
open import Data.Rational.Properties

1/4 : ℚ
1/4 = + 1 / 4

3/4 : ℚ
3/4 = + 3 / 4

-- Some binary operators are also defined, including addition,
-- subtraction and multiplication.

expr : ℚ
expr = (1/4 + ½) * 1ℚ - 0ℚ

-- We can use PropositionalEquality with rational numbers

open import Relation.Binary.PropositionalEquality -- using (_≡_; refl)

eqEx : expr ≡ 3/4
eqEx = refl

-- or use equality defined for rational numbers

eqEx' : expr ≃ 3/4
eqEx' = *≡* refl

-- we can automaticaly prove equations using RingSolver

open import Data.Rational.Tactic.RingSolver

lemma : ∀ (x y : ℚ) → x + y + 1/4 + ½ ≃ 3/4 + y + x
{-
Malformed call to solve.Expected target type to be like: ∀ x y → x + y ≈ y + x.Instead: _19
when checking that the expression unquote solve-∀ has type _19
-}
lemma = {! solve-∀  !}
