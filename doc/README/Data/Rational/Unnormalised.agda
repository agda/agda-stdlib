------------------------------------------------------------------------
-- The Agda standard library
--
-- Some examples showing where the unnormalised rational numbers and some
-- related operations and properties are defined, and how they can be used
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible #-}

module README.Data.Rational.Unnormalised where

open import Data.Integer using (+_)
open import Data.Rational.Unnormalised
open import Data.Rational.Unnormalised.Properties

1/4 : ℚᵘ
1/4 = + 1 / 4

3/4 : ℚᵘ
3/4 = + 3 / 4

expr : ℚᵘ
expr = (1/4 + ½) * 1ℚᵘ - 0ℚᵘ

expr2 : expr ≃ 3/4
expr2 = *≡* refl

open import Data.Rational.Unnormalised.Tactic.RingSolver

lemma₁ : ∀ (x y : ℚᵘ) → x + y + 1/4 + ½ ≃ 3/4 + y + x
lemma₁ = solve-∀
