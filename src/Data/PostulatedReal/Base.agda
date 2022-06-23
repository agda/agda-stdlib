------------------------------------------------------------------------
-- The Agda standard library
--
-- Postulated Real numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.PostulatedReal.Base where

open import Data.Empty.Irrelevant
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; ≢-sym)

postulate
  ℝ     : Set
  0ℝ 1ℝ : ℝ
  1≢0   : 1ℝ ≢ 0ℝ

------------------------------------------------------------------------
-- Ordering of reals

infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≱_ _≮_ _≯_

postulate
  _≤_ : Rel ℝ 0ℓ

data _<_ : Rel ℝ 0ℓ where
  *<* : ∀ {x y} → x ≤ y → x ≢ y → x < y

_≥_ : Rel ℝ 0ℓ
x ≥ y = y ≤ x

_>_ : Rel ℝ 0ℓ
x > y = y < x

_≰_ : Rel ℝ 0ℓ
x ≰ y = ¬ (x ≤ y)

_≱_ : Rel ℝ 0ℓ
x ≱ y = ¬ (x ≥ y)

_≮_ : Rel ℝ 0ℓ
x ≮ y = ¬ (x < y)

_≯_ : Rel ℝ 0ℓ
x ≯ y = ¬ (x > y)

------------------------------------------------------------------------
-- Simple predicates

record NonZero (x : ℝ) : Set where
  field nonZero : x ≢ 0ℝ

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

-- Destructors

≢-nonZero⁻¹ : ∀ x → .{{NonZero x}} → x ≢ 0ℝ
≢-nonZero⁻¹ _ ⦃ p ⦄ x≡0 = ⊥-elim (NonZero.nonZero p x≡0)

------------------------------------------------------------------------------
-- Operations on reals

infix  8 -_ 1/_
infixl 7 _*_ _/_
infixl 6 _-_ _+_

postulate
  _+_ : ℝ → ℝ → ℝ
  -_  : ℝ → ℝ
  _*_ : ℝ → ℝ → ℝ
  1/_ : (x : ℝ) .⦃ _ : NonZero x ⦄ → ℝ

_-_ : ℝ → ℝ → ℝ
x - y = x + (- y)

_/_ : ℝ → (y : ℝ) .⦃ _ : NonZero y ⦄ → ℝ
x / y = x * 1/ y

------------------------------------------------------------------------------
-- Some constants

-1ℝ : ℝ
-1ℝ = - 1ℝ

