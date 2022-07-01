------------------------------------------------------------------------
-- The Agda standard library
--
-- ParametrizedReal numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.ParametrizedReal.Interface

module Data.ParametrizedReal.Base (RealInterface : Reals) where

open import Data.Empty.Irrelevant
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; ≢-sym)

open RealsCore (Reals.core RealInterface) public
open RealsOps (Reals.ops RealInterface) using (_+_; -_; _*_; 1/_) public

------------------------------------------------------------------------
-- Simple predicates

-- Instances

instance
  1-nonZero : NonZero 1ℝ
  1-nonZero = record {nonZero = 1≢0}

-- Constructors

≢-nonZero : ∀ {x} → x ≢ 0ℝ → NonZero x
≢-nonZero x≢0 = record {nonZero = x≢0}

<-nonZero : ∀ {x} → x < 0ℝ → NonZero x
<-nonZero (*<* _ x≢0) = record {nonZero = x≢0}

>-nonZero : ∀ {x} → x > 0ℝ → NonZero x
>-nonZero (*<* _ 0≢x) = record {nonZero = ≢-sym 0≢x}

positive : ∀ {x} → x > 0ℝ → Positive x
positive x>0 = record {positive = x>0}

negative : ∀ {x} → x < 0ℝ → Negative x
negative x<0 = record {negative = x<0}

nonPositive : ∀ {x} → x ≤ 0ℝ → NonPositive x
nonPositive x≤0 = record {nonPositive = x≤0}

nonNegative : ∀ {x} → x ≥ 0ℝ → NonNegative x
nonNegative x≥0 = record {nonNegative = x≥0}

-- Destructors

≢-nonZero⁻¹ : ∀ x → .⦃ NonZero x ⦄ → x ≢ 0ℝ
≢-nonZero⁻¹ _ ⦃ p ⦄ x≡0 = ⊥-elim (NonZero.nonZero p x≡0)

positive⁻¹ : ∀ x → ⦃ Positive x ⦄ → x > 0ℝ
positive⁻¹ _ ⦃ p ⦄ = Positive.positive p

negative⁻¹ : ∀ x → ⦃ Negative x ⦄ → x < 0ℝ
negative⁻¹ _ ⦃ p ⦄ = Negative.negative p

nonPositive⁻¹ : ∀ x → ⦃ NonPositive x ⦄ → x ≤ 0ℝ
nonPositive⁻¹ _ ⦃ p ⦄ = NonPositive.nonPositive p

nonNegative⁻¹ : ∀ x → ⦃ NonNegative x ⦄ → x ≥ 0ℝ
nonNegative⁻¹ _ ⦃ p ⦄ = NonNegative.nonNegative p

------------------------------------------------------------------------
-- Operations on reals

infixl 7 _/_
infixl 6 _-_

_-_ : ℝ → ℝ → ℝ
x - y = x + (- y)

_/_ : ℝ → (y : ℝ) .⦃ _ : NonZero y ⦄ → ℝ
x / y = x * 1/ y

------------------------------------------------------------------------
-- Some constants

-1ℝ : ℝ
-1ℝ = - 1ℝ

