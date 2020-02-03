------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Base where

open import Function using (id)
open import Data.Integer.Base as ℤ using (ℤ; ∣_∣; +_; -[1+_])
import Data.Integer.GCD as ℤ
import Data.Integer.DivMod as ℤ
open import Data.Nat.GCD
open import Data.Nat.Divisibility as ℕDiv using (divides; 0∣⇒≡0)
open import Data.Nat.Coprimality as C using (Coprime; Bézout-coprime; coprime-/gcd)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc) hiding (module ℕ)
import Data.Nat.DivMod as ℕ
open import Data.Rational.Unnormalised using (ℚᵘ; mkℚᵘ; _≢0)
open import Data.Product
open import Data.Sum.Base using (inj₂)
open import Level using (0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse; toWitnessFalse)
open import Relation.Nullary.Negation using (contradiction)
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
    .isCoprime    : Coprime ∣ numerator ∣ (suc denominator-1)

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

------------------------------------------------------------------------------
-- Operations on rationals

infix  8 -_ 1/_
infixl 7 _*_ _÷_
infixl 6 _-_ _+_

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

1/_ : (p : ℚ) → .{n≢0 : ∣ ↥ p ∣ ≢0} → ℚ
1/ mkℚ +[1+ n ] d prf = mkℚ +[1+ d ] n (C.sym prf)
1/ mkℚ -[1+ n ] d prf = mkℚ -[1+ d ] n (C.sym prf)

-- division: requires a proof that the denominator is not zero

_÷_ : (p q : ℚ) → .{n≢0 : ∣ ↥ q ∣ ≢0} → ℚ
(p ÷ q) {n≢0} = p * (1/ q) {n≢0}

------------------------------------------------------------------------
-- Conversion to and from unnormalized rationals

toℚᵘ : ℚ → ℚᵘ
toℚᵘ (mkℚ n d-1 _) = mkℚᵘ n d-1

fromℚᵘ : ℚᵘ → ℚ
fromℚᵘ (mkℚᵘ n d-1) = n / suc d-1
