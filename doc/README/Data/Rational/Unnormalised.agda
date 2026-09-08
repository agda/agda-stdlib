module README.Data.Rational.Unnormalised where

open import Data.Integer using (+_)
open import Data.Rational.Unnormalised
open import Data.Rational.Unnormalised.Properties
open import Relation.Binary.PropositionalEquality using (refl)

1/4 : ℚᵘ
1/4 = + 1 / 4

3/4 : ℚᵘ
3/4 = + 3 / 4

6/8 : ℚᵘ
6/8 = + 6 / 8

expr : ℚᵘ
expr = (1/4 + ½) * 1ℚᵘ - 0ℚᵘ

eqEx : expr ≃ 3/4
eqEx = *≡* refl

open import Data.Rational.Unnormalised.Tactic.RingSolver

lemma₁ : ∀ (x y : ℚᵘ) → x + y + 1/4 + ½ ≃ 6/8 + y + x
lemma₁ = solve-∀
