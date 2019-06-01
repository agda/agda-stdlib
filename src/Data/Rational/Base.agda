------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Base where

open import Function using (id)
open import Data.Integer as ℤ using (ℤ; ∣_∣; +_; -[1+_])
open import Data.Nat.GCD
open import Data.Nat.Divisibility as ℕDiv using (divides; 0∣⇒≡0)
open import Data.Nat.Coprimality as C using (Coprime; Bézout-coprime)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product
open import Level using (0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (False)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; cong; cong₂; module ≡-Reasoning)

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

infix 4 _≢0
_≢0 : ℕ → Set
n ≢0 = False (n ℕ.≟ 0)

-- A constructor for ℚ that takes two natural numbers, say 6 and 21,
-- and returns them in a normalized form, e.g. say 2 and 7

normalize : ∀ (m n : ℕ) → .{n≢0 : n ≢0} → ℚ
normalize zero    n       = mkℚ +0 0 (C.sym (C.1-coprimeTo 0))
normalize (suc m) (suc n) with mkGCD (suc m) (suc n)
... | zero  , GCD.is (1+m∣0 , _) _ = contradiction (0∣⇒≡0 1+m∣0) λ()
... | suc g , G@(GCD.is (divides (suc p) refl , divides (suc q) refl) _)
  = mkℚ (+ suc p) q (Bézout-coprime (Bézout.identity G))

-- A constructor for ℚ that (unlike mkℚ) automatically normalises it's
-- arguments. See the constants section below for how to use this operator.

infixl 7 _/_

_/_ : (n : ℤ) (d : ℕ) → .{d≢0 : d ≢0} → ℚ
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
(p ÷ q) {n≢0} = p * (1/_ q {n≢0})
