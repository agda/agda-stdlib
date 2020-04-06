------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers in non-reduced form.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Unnormalised where

open import Data.Integer.Base as ℤ using (ℤ; ∣_∣; +0; +[1+_]; -[1+_])
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (∃; ∃-syntax; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (False; True)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)

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
  denominator = ℤ.+ denominatorℕ

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
-- Non-negative and negative rationals

record non-neg (p : ℚᵘ) : Set where
  constructor _,_
  field
    numerator : ℕ
    proof : ↥ p ≡ ℤ.+ numerator

open non-neg public using (proof)
  renaming
  ( numerator    to ↥+_
  )

neg : ℚᵘ → Set
neg = ¬_ ∘ non-neg

ℚᵘ+ : Set
ℚᵘ+ = ∃ non-neg

------------------------------------------------------------------------
-- Positive and non-positive rationals

record pos (p : ℚᵘ) : Set where
  constructor _,_
  field
    numerator : ℕ
    proof : ↥ p ≡ ℤ.+ (suc numerator)

open pos public using (proof)
  renaming
  ( numerator    to ↥*+_
  )

non-pos : ℚᵘ → Set
non-pos = ¬_ ∘ pos

ℚᵘ*+ : Set
ℚᵘ*+ = ∃ pos

------------------------------------------------------------------------
-- Constructing rationals

mkℚᵘ+ : ∀ (n : ℕ) dm → ℚᵘ
mkℚᵘ+ n dm = mkℚᵘ (ℤ.+ n) dm

mkℚᵘ*+ : ∀ (n : ℕ) dm → ℚᵘ
mkℚᵘ*+ n dm = mkℚᵘ (ℤ.+ (suc n)) dm

mkℚᵘ*- : ∀ (n : ℕ) dm → ℚᵘ
mkℚᵘ*- n dm = mkℚᵘ -[1+ n ]  dm

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
0ℚᵘ = ℤ.+ 0 / 1

1ℚᵘ : ℚᵘ
1ℚᵘ = ℤ.+ 1 / 1

½ : ℚᵘ
½ = ℤ.+ 1 / 2

-½ : ℚᵘ
-½ = - ½
