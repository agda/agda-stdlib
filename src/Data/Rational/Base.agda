------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Base where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Function.Base using (id)
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; -[1+_])
import Data.Integer.GCD as ℤ
import Data.Integer.DivMod as ℤ
open import Data.Nat.GCD
open import Data.Nat.Divisibility as ℕDiv using (divides; 0∣⇒≡0)
open import Data.Nat.Coprimality as C
  using (Coprime; Bézout-coprime; coprime-/gcd; coprime?; ¬0-coprimeTo-2+)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc) hiding (module ℕ)
import Data.Nat.DivMod as ℕ
open import Data.Rational.Unnormalised.Base as ℚᵘ using (ℚᵘ; mkℚᵘ; _≢0)
open import Data.Product
open import Data.Sign using (Sign)
open import Data.Sum.Base using (inj₂)
open import Level using (0ℓ)
open import Relation.Nullary using (¬_; recompute)
open import Relation.Nullary.Decidable
  using (False; fromWitness; fromWitnessFalse; toWitnessFalse)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; cong; cong₂; module ≡-Reasoning)

open ≡-Reasoning

-- Note, these are re-exported publicly to maintain backwards
-- compatability. Although we are unable (?) to put a warning on them,
-- using these from `Data.Rational` should be viewed as a deprecated
-- feature.

open import Data.Integer public using (+0; +[1+_])

------------------------------------------------------------------------
-- Rational numbers in reduced form. Note that there is exactly one
-- way to represent every rational number.

record ℚ : Set where
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

mkℚ+ : ∀ n d → .{d≢0 : d ≢0} → .(Coprime n d) → ℚ
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

normalize : ∀ (m n : ℕ) {n≢0 : n ≢0} → ℚ
normalize m n {n≢0} = mkℚ+ (m ℕ./ gcd m n) (n ℕ./ gcd m n)
  {n/g≢0} (coprime-/gcd m n {g≢0})
  where
  g≢0   = fromWitnessFalse (gcd[m,n]≢0 m n (inj₂ (toWitnessFalse n≢0)))
  n/g≢0 = fromWitnessFalse (n/gcd[m,n]≢0 m n {n≢0} {g≢0})

-- A constructor for ℚ that (unlike mkℚ) automatically normalises it's
-- arguments. See the constants section below for how to use this operator.

infixl 7 _/_

_/_ : (n : ℤ) (d : ℕ) → {d≢0 : d ≢0} → ℚ
(+ n      / d) {d≢0} =   normalize n       d {d≢0}
(-[1+ n ] / d) {d≢0} = - normalize (suc n) d {d≢0}

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
≢-nonZero {mkℚ +0       zero    _} p≢0 = p≢0 refl
≢-nonZero {mkℚ +0       (suc d) c} p≢0 = ¬0-coprimeTo-2+ (C.recompute c)

>-nonZero : ∀ {p} → p > 0ℚ → NonZero p
>-nonZero {p} (*<* p<q) = ℚᵘ.>-nonZero {toℚᵘ p} (ℚᵘ.*<* p<q)

<-nonZero : ∀ {p} → p < 0ℚ → NonZero p
<-nonZero {p} (*<* p<q) = ℚᵘ.<-nonZero {toℚᵘ p} (ℚᵘ.*<* p<q)

positive : ∀ {p} → p > 0ℚ → Positive p
positive {p} (*<* p<q) = ℚᵘ.positive {toℚᵘ p} (ℚᵘ.*<* p<q)

negative : ∀ {p} → p < 0ℚ → Negative p
negative {p} (*<* p<q) = ℚᵘ.negative {toℚᵘ p} (ℚᵘ.*<* p<q)

nonPositive : ∀ {p} → p ≤ 0ℚ → NonPositive p
nonPositive {p} (*≤* p≤q) = ℚᵘ.nonPositive {toℚᵘ p} (ℚᵘ.*≤* p≤q)

nonNegative : ∀ {p} → p ≥ 0ℚ → NonNegative p
nonNegative {p} (*≤* p≤q) = ℚᵘ.nonNegative {toℚᵘ p} (ℚᵘ.*≤* p≤q)

------------------------------------------------------------------------------
-- Operations on rationals

infix  8 -_ 1/_
infixl 7 _*_ _÷_ _⊓_
infixl 6 _-_ _+_ _⊔_

-- addition
_+_ : ℚ → ℚ → ℚ
p + q = (↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p) / (↧ₙ p ℕ.* ↧ₙ q)

-- multiplication
_*_ : ℚ → ℚ → ℚ
p * q = (↥ p ℤ.* ↥ q) / (↧ₙ p ℕ.* ↧ₙ q)

-- subtraction
_-_ : ℚ → ℚ → ℚ
p - q = p + (- q)

-- reciprocal: requires a proof that the numerator is not zero
1/_ : (p : ℚ) → .{n≢0 : ℤ.∣ ↥ p ∣ ≢0} → ℚ
1/ mkℚ +[1+ n ] d prf = mkℚ +[1+ d ] n (C.sym prf)
1/ mkℚ -[1+ n ] d prf = mkℚ -[1+ d ] n (C.sym prf)

-- division: requires a proof that the denominator is not zero
_÷_ : (p q : ℚ) → .{n≢0 : ℤ.∣ ↥ q ∣ ≢0} → ℚ
(p ÷ q) {n≢0} = p * (1/ q) {n≢0}

-- max
_⊔_ : (p q : ℚ) → ℚ
p ⊔ q = if p ≤ᵇ q then q else p

-- min
_⊓_ : (p q : ℚ) → ℚ
p ⊓ q = if p ≤ᵇ q then p else q

-- absolute value
∣_∣ : ℚ → ℚ
∣ mkℚ n d c ∣ = mkℚ (+ ℤ.∣ n ∣) d c
