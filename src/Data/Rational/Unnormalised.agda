------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers in non-reduced form.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Unnormalised where

open import Data.Integer as ℤ using (ℤ; ∣_∣; +_; +0; +[1+_]; -[1+_])
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Level using (0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (False)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)

------------------------------------------------------------------------
-- Definition

-- Here we define rationals that are not necessarily in reduced form.
-- Consequently there are multiple ways of representing a given rational
-- number, and the performance of the arithmetic operations may suffer
-- due to blowup of the numerator and denominator.

-- Nonetheless they are much easier to reason about. In general proofs
-- are first proved for these unnormalised rationals and then translated
-- into the normalised rationals.

record ℚᵘ : Set where
  constructor mkℚᵘ
  field
    numerator     : ℤ
    denominator-1 : ℕ

  denominatorℕ : ℕ
  denominatorℕ = suc denominator-1

  denominator : ℤ
  denominator = + denominatorℕ

open ℚᵘ public using ()
  renaming
  ( numerator    to ↥_
  ; denominator  to ↧_
  ; denominatorℕ to ↧ₙ_
  )

------------------------------------------------------------------------
-- Equality of rational numbers (does not coincide with _≡_)

infix 4 _≃_
data _≃_ : Rel ℚᵘ 0ℓ where
  *≡* : ∀ {p q} → (↥ p ℤ.* ↧ q) ≡ (↥ q ℤ.* ↧ p) → p ≃ q

------------------------------------------------------------------------
-- Ordering of rationals

infix 4 _≤_ _<_ _≥_ _>_ _≰_ _≱_ _≮_ _≯_

data _≤_ : Rel ℚᵘ 0ℓ where
  *≤* : ∀ {p q} → (↥ p ℤ.* ↧ q) ℤ.≤ (↥ q ℤ.* ↧ p) → p ≤ q

data _<_ : Rel ℚᵘ 0ℓ where
  *<* : ∀ {p q} → (↥ p ℤ.* ↧ q) ℤ.< (↥ q ℤ.* ↧ p) → p < q

_≥_ : Rel ℚᵘ 0ℓ
x ≥ y = y ≤ x

_>_ : Rel ℚᵘ 0ℓ
x > y = y < x

_≰_ : Rel ℚᵘ 0ℓ
x ≰ y = ¬ (x ≤ y)

_≱_ : Rel ℚᵘ 0ℓ
x ≱ y = ¬ (x ≥ y)

_≮_ : Rel ℚᵘ 0ℓ
x ≮ y = ¬ (x < y)

_≯_ : Rel ℚᵘ 0ℓ
x ≯ y = ¬ (x > y)

------------------------------------------------------------------------
-- Constructing rationals

infix 4 _≢0
_≢0 : ℕ → Set
n ≢0 = False (n ℕ.≟ 0)

-- An alternative constructor for ℚᵘ. See the constants section below
-- for examples of how to use this operator.

infixl 7 _/_

_/_ : (n : ℤ) (d : ℕ) .{d≢0 : d ≢0} → ℚᵘ
n / suc d = mkℚᵘ n d

------------------------------------------------------------------------------
-- Operations on rationals

infix  8 -_ 1/_
infixl 7 _*_ _÷_
infixl 6 _-_ _+_

-- negation

-_ : ℚᵘ → ℚᵘ
- mkℚᵘ n d = mkℚᵘ (ℤ.- n) d

-- addition

_+_ : ℚᵘ → ℚᵘ → ℚᵘ
p + q = (↥ p ℤ.* ↧ q ℤ.+ ↥ q ℤ.* ↧ p) / (↧ₙ p ℕ.* ↧ₙ q)

-- multiplication

_*_ : ℚᵘ → ℚᵘ → ℚᵘ
p * q = (↥ p ℤ.* ↥ q) / (↧ₙ p ℕ.* ↧ₙ q)

-- subtraction

_-_ : ℚᵘ → ℚᵘ → ℚᵘ
p - q = p + (- q)

-- reciprocal: requires a proof that the numerator is not zero

1/_ : (p : ℚᵘ) → .{n≢0 : ∣ ↥ p ∣ ≢0} → ℚᵘ
1/ mkℚᵘ +[1+ n ] d = mkℚᵘ +[1+ d ] n
1/ mkℚᵘ -[1+ n ] d = mkℚᵘ -[1+ d ] n

-- division: requires a proof that the denominator is not zero

_÷_ : (p q : ℚᵘ) → .{n≢0 : ∣ ↥ q ∣ ≢0} → ℚᵘ
(p ÷ q) {n≢0} = p * (1/_ q {n≢0})

------------------------------------------------------------------------------
-- Some constants

0ℚᵘ : ℚᵘ
0ℚᵘ = + 0 / 1

1ℚᵘ : ℚᵘ
1ℚᵘ = + 1 / 1

½ : ℚᵘ
½ = + 1 / 2

-½ : ℚᵘ
-½ = - ½
