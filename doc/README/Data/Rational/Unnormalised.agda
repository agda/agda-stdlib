------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing where the unnormalised rational numbers and some
-- related operations and properties are defined, and how they can be used
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module README.Data.Rational.Unnormalised where

-- The rational numbers and various arithmetic operations are defined in
-- Data.Rational.

open import Data.Integer using (+_)
open import Data.Rational.Unnormalised
open import Data.Rational.Unnormalised.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

1/4 : ℚᵘ
1/4 = + 1 / 4

3/4 : ℚᵘ
3/4 = + 3 / 4

-- Some binary operators are also defined, including addition,
-- subtraction and multiplication.

expr : ℚᵘ
expr = (1/4 + ½) * 1ℚᵘ - 0ℚᵘ

-- We can use defined for rational numbers

expr2 : expr ≃ 3/4
expr2 = *≡* refl

-- We can automatically proove equations using Ring

open import Data.Rational.Unnormalised.Tactic.RingSolver

lemma₁ : ∀ (x y : ℚᵘ) → (x + y) ≡ (y + x) -- TODO should we use ≃
{-
TODO fails with:
Malformed call to solve.Expected target type to be like: ∀ x y → x + y ≈ y + x.Instead: _25
when checking that the expression unquote solve-∀ has type _25
-}
lemma₁ = {! solve-∀  !}
