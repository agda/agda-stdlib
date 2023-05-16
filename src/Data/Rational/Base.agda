------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Base where

open import Algebra.Bundles.Raw
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; +[1+_]; -[1+_])
open import Data.Nat.GCD
open import Data.Nat.Coprimality as C
  using (Coprime; Bézout-coprime; coprime-/gcd; coprime?; ¬0-coprimeTo-2+)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc) hiding (module ℕ)
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ)
open import Data.Sum.Base using (inj₂)
open import Function.Base using (id)
open import Level using (0ℓ)
open import Relation.Nullary using (¬_; recompute)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl)

------------------------------------------------------------------------
-- Rational numbers in reduced form. Note that there is exactly one
-- way to represent every rational number.

record ℚ : Set where
  -- We add "no-eta-equality; pattern" to the record to stop Agda
  -- automatically unfolding rationals when arithmetic operations are
  -- applied to them (see definition of operators below and Issue #1753
  -- for details).
  no-eta-equality; pattern

  constructor mkℚ
  field
    numerator     : ℤ
    denominator-1 : ℕ
    .isCoprime    : Coprime ℤ.∣ numerator ∣ (suc denominator-1)

  denominatorℕ : ℕ
  denominatorℕ = suc denominator-1

  denominator : ℤ
  denominator = + denominatorℕ

open ℚ public using ()
  renaming
  ( numerator    to ↥_
  ; denominator  to ↧_
  ; denominatorℕ to ↧ₙ_
  )

mkℚ+ : ∀ n d → .{{_ : ℕ.NonZero d}} → .(Coprime n d) → ℚ
mkℚ+ n (suc d) coprime = mkℚ (+ n) d coprime

------------------------------------------------------------------------
-- Equality of rational numbers (coincides with _≡_)

infix 4 _≃_

_≃_ : Rel ℚ 0ℓ
p ≃ q = (↥ p ℤ.* ↧ q) ≡ (↥ q ℤ.* ↧ p)

------------------------------------------------------------------------
-- Ordering of rationals

infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≱_ _≮_ _≯_

data _≤_ : Rel ℚ 0ℓ where
  *≤* : ∀ {p q} → (↥ p ℤ.* ↧ q) ℤ.≤ (↥ q ℤ.* ↧ p) → p ≤ q

data _<_ : Rel ℚ 0ℓ where
  *<* : ∀ {p q} → (↥ p ℤ.* ↧ q) ℤ.< (↥ q ℤ.* ↧ p) → p < q

_≥_ : Rel ℚ 0ℓ
x ≥ y = y ≤ x

_>_ : Rel ℚ 0ℓ
x > y = y < x

_≰_ : Rel ℚ 0ℓ
x ≰ y = ¬ (x ≤ y)

_≱_ : Rel ℚ 0ℓ
x ≱ y = ¬ (x ≥ y)

_≮_ : Rel ℚ 0ℓ
x ≮ y = ¬ (x < y)

_≯_ : Rel ℚ 0ℓ
x ≯ y = ¬ (x > y)

------------------------------------------------------------------------
-- Boolean ordering

infix 4 _≤ᵇ_

_≤ᵇ_ : ℚ → ℚ → Bool
p ≤ᵇ q = (↥ p ℤ.* ↧ q) ℤ.≤ᵇ (↥ q ℤ.* ↧ p)

------------------------------------------------------------------------
-- Negation

-_ : ℚ → ℚ
- mkℚ -[1+ n ] d prf = mkℚ +[1+ n ] d prf
- mkℚ +0       d prf = mkℚ +0       d prf
- mkℚ +[1+ n ] d prf = mkℚ -[1+ n ] d prf

------------------------------------------------------------------------
-- Constructing rationals

-- A constructor for ℚ that takes two natural numbers, say 6 and 21,
-- and returns them in a normalized form, e.g. say 2 and 7

normalize : ∀ (m n : ℕ) .{{_ : ℕ.NonZero n}} → ℚ
normalize m n = mkℚ+ (m ℕ./ gcd m n) (n ℕ./ gcd m n) (coprime-/gcd m n)
  where
    instance
      g≢0   = ℕ.≢-nonZero (gcd[m,n]≢0 m n (inj₂ (ℕ.≢-nonZero⁻¹ n)))
      n/g≢0 = ℕ.≢-nonZero (n/gcd[m,n]≢0 m n {{gcd≢0 = g≢0}})

-- A constructor for ℚ that (unlike mkℚ) automatically normalises it's
-- arguments. See the constants section below for how to use this operator.

infixl 7 _/_

_/_ : (n : ℤ) (d : ℕ) → .{{_ : ℕ.NonZero d}} → ℚ
(+ n      / d) =   normalize n       d
(-[1+ n ] / d) = - normalize (suc n) d

------------------------------------------------------------------------
-- Conversion to and from unnormalized rationals

toℚᵘ : ℚ → ℚᵘ
toℚᵘ (mkℚ n d-1 _) = mkℚᵘ n d-1

fromℚᵘ : ℚᵘ → ℚ
fromℚᵘ (mkℚᵘ n d-1) = n / suc d-1

------------------------------------------------------------------------------
-- Some constants

0ℚ : ℚ
0ℚ = + 0 / 1

1ℚ : ℚ
1ℚ = + 1 / 1

½ : ℚ
½ = + 1 / 2

-½ : ℚ
-½ = - ½

------------------------------------------------------------------------
-- Simple predicates

NonZero : Pred ℚ 0ℓ
NonZero p = ℚᵘ.NonZero (toℚᵘ p)

Positive : Pred ℚ 0ℓ
Positive p = ℚᵘ.Positive (toℚᵘ p)

Negative : Pred ℚ 0ℓ
Negative p = ℚᵘ.Negative (toℚᵘ p)

NonPositive : Pred ℚ 0ℓ
NonPositive p = ℚᵘ.NonPositive (toℚᵘ p)

NonNegative : Pred ℚ 0ℓ
NonNegative p = ℚᵘ.NonNegative (toℚᵘ p)

-- Constructors

≢-nonZero : ∀ {p} → p ≢ 0ℚ → NonZero p
≢-nonZero {mkℚ -[1+ _ ] _       _} _   = _
≢-nonZero {mkℚ +[1+ _ ] _       _} _   = _
≢-nonZero {mkℚ +0       zero    _} p≢0 = contradiction refl p≢0
≢-nonZero {mkℚ +0       (suc d) c} p≢0 = contradiction (λ {i} → C.recompute c {i}) ¬0-coprimeTo-2+

>-nonZero : ∀ {p} → p > 0ℚ → NonZero p
>-nonZero {p@(mkℚ _ _ _)} (*<* p<q) = ℚᵘ.>-nonZero {toℚᵘ p} (ℚᵘ.*<* p<q)

<-nonZero : ∀ {p} → p < 0ℚ → NonZero p
<-nonZero {p@(mkℚ _ _ _)} (*<* p<q) = ℚᵘ.<-nonZero {toℚᵘ p} (ℚᵘ.*<* p<q)

positive : ∀ {p} → p > 0ℚ → Positive p
positive {p@(mkℚ _ _ _)} (*<* p<q) = ℚᵘ.positive {toℚᵘ p} (ℚᵘ.*<* p<q)

negative : ∀ {p} → p < 0ℚ → Negative p
negative {p@(mkℚ _ _ _)} (*<* p<q) = ℚᵘ.negative {toℚᵘ p} (ℚᵘ.*<* p<q)

nonPositive : ∀ {p} → p ≤ 0ℚ → NonPositive p
nonPositive {p@(mkℚ _ _ _)} (*≤* p≤q) = ℚᵘ.nonPositive {toℚᵘ p} (ℚᵘ.*≤* p≤q)

nonNegative : ∀ {p} → p ≥ 0ℚ → NonNegative p
nonNegative {p@(mkℚ _ _ _)} (*≤* p≤q) = ℚᵘ.nonNegative {toℚᵘ p} (ℚᵘ.*≤* p≤q)

------------------------------------------------------------------------------
-- Operations on rationals

-- For explanation of the `@record{}` annotations see notes in the equivalent
-- place in `Data.Rational.Unnormalised.Base`.

infix  8 -_ 1/_
infixl 7 _*_ _÷_ _⊓_
infixl 6 _-_ _+_ _⊔_

-- addition
_+_ : ℚ → ℚ → ℚ
p@record{} + q@record{} = (↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p) / (↧ₙ p ℕ.* ↧ₙ q)

-- multiplication
_*_ : ℚ → ℚ → ℚ
p@record{} * q@record{} = (↥ p ℤ.* ↥ q) / (↧ₙ p ℕ.* ↧ₙ q)

-- subtraction
_-_ : ℚ → ℚ → ℚ
p - q = p + (- q)

-- reciprocal: requires a proof that the numerator is not zero
1/_ : (p : ℚ) → .{{_ : NonZero p}} → ℚ
1/ mkℚ +[1+ n ] d prf = mkℚ +[1+ d ] n (C.sym prf)
1/ mkℚ -[1+ n ] d prf = mkℚ -[1+ d ] n (C.sym prf)

-- division: requires a proof that the denominator is not zero
_÷_ : (p q : ℚ) → .{{_ : NonZero q}} → ℚ
p ÷ q = p * (1/ q)

-- max
_⊔_ : (p q : ℚ) → ℚ
p@record{} ⊔ q@record{} = if p ≤ᵇ q then q else p

-- min
_⊓_ : (p q : ℚ) → ℚ
p@record{} ⊓ q@record{} = if p ≤ᵇ q then p else q

-- absolute value
∣_∣ : ℚ → ℚ
∣ mkℚ n d c ∣ = mkℚ (+ ℤ.∣ n ∣) d c

------------------------------------------------------------------------
-- Rounding functions

-- Floor (round towards -∞)
floor : ℚ → ℤ
floor p@record{} = ↥ p ℤ./ ↧ p

-- Ceiling (round towards +∞)
ceiling : ℚ → ℤ
ceiling p@record{} = ℤ.- floor (- p)

-- Truncate  (round towards 0)
truncate : ℚ → ℤ
truncate p with p ≤ᵇ 0ℚ
... | true  = ceiling p
... | false = floor p

-- Round (to nearest integer)
round : ℚ → ℤ
round p with p ≤ᵇ 0ℚ
... | true  = ceiling (p - ½)
... | false = floor (p + ½)

-- Fractional part (remainder after floor)
fracPart : ℚ → ℚ
fracPart p@record{} = ∣ p - truncate p / 1 ∣

-- Extra notations  ⌊ ⌋ floor,  ⌈ ⌉ ceiling,  [ ] truncate
syntax floor p = ⌊ p ⌋
syntax ceiling p = ⌈ p ⌉
syntax truncate p = [ p ]

------------------------------------------------------------------------
-- Raw bundles

+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  }

+-0-rawMonoid : RawMonoid 0ℓ 0ℓ
+-0-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  ; ε   = 0ℚ
  }

+-0-rawGroup : RawGroup 0ℓ 0ℓ
+-0-rawGroup = record
  { _≈_ = _≡_
  ; _∙_ = _+_
  ; ε   = 0ℚ
  ; _⁻¹ = -_
  }

+-*-rawNearSemiring : RawNearSemiring 0ℓ 0ℓ
+-*-rawNearSemiring = record
  { _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0#  = 0ℚ
  }

+-*-rawSemiring : RawSemiring 0ℓ 0ℓ
+-*-rawSemiring = record
  { _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0#  = 0ℚ
  ; 1#  = 1ℚ
  }

+-*-rawRing : RawRing 0ℓ 0ℓ
+-*-rawRing = record
  { _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_  = -_
  ; 0#  = 0ℚ
  ; 1#  = 1ℚ
  }

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  }

*-1-rawMonoid : RawMonoid 0ℓ 0ℓ
*-1-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  ; ε   = 1ℚ
  }


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

+-rawMonoid = +-0-rawMonoid
{-# WARNING_ON_USAGE +-rawMonoid
"Warning: +-rawMonoid was deprecated in v2.0
Please use +-0-rawMonoid instead."
#-}
*-rawMonoid = *-1-rawMonoid
{-# WARNING_ON_USAGE *-rawMonoid
"Warning: *-rawMonoid was deprecated in v2.0
Please use *-1-rawMonoid instead."
#-}
