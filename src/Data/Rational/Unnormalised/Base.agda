------------------------------------------------------------------------
-- The Agda standard library
--
-- Rational numbers in non-reduced form.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Unnormalised.Base where

open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; +0; +[1+_]; -[1+_]; +<+; +≤+)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Level using (0ℓ)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (False)
open import Relation.Unary using (Pred)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl)

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

infix 4 _≃_ _≠_

data _≃_ : Rel ℚᵘ 0ℓ where
  *≡* : ∀ {p q} → (↥ p ℤ.* ↧ q) ≡ (↥ q ℤ.* ↧ p) → p ≃ q

_≠_ : Rel ℚᵘ 0ℓ
p ≠ q = ¬ (p ≃ q)

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
-- Boolean ordering

infix 4 _≤ᵇ_

_≤ᵇ_ : ℚᵘ → ℚᵘ → Bool
p ≤ᵇ q = (↥ p ℤ.* ↧ q) ℤ.≤ᵇ (↥ q ℤ.* ↧ p)

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
infixl 7 _*_ _÷_ _⊓_
infixl 6 _-_ _+_ _⊔_

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

1/_ : (p : ℚᵘ) → .{n≢0 : ℤ.∣ ↥ p ∣ ≢0} → ℚᵘ
1/ mkℚᵘ +[1+ n ] d = mkℚᵘ +[1+ d ] n
1/ mkℚᵘ -[1+ n ] d = mkℚᵘ -[1+ d ] n

-- division: requires a proof that the denominator is not zero

_÷_ : (p q : ℚᵘ) → .{n≢0 : ℤ.∣ ↥ q ∣ ≢0} → ℚᵘ
(p ÷ q) {n≢0} = p * (1/_ q {n≢0})

-- max
_⊔_ : (p q : ℚᵘ) → ℚᵘ
p ⊔ q = if p ≤ᵇ q then q else p

-- min
_⊓_ : (p q : ℚᵘ) → ℚᵘ
p ⊓ q = if p ≤ᵇ q then p else q

-- absolute value
∣_∣ : ℚᵘ → ℚᵘ
∣ mkℚᵘ p q ∣ = mkℚᵘ (+ ℤ.∣ p ∣) q

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

------------------------------------------------------------------------
-- Simple predicates

NonZero : Pred ℚᵘ 0ℓ
NonZero p = ℤ.NonZero (↥ p)

Positive : Pred ℚᵘ 0ℓ
Positive p = ℤ.Positive (↥ p)

Negative : Pred ℚᵘ 0ℓ
Negative p = ℤ.Negative (↥ p)

NonPositive : Pred ℚᵘ 0ℓ
NonPositive p = ℤ.NonPositive (↥ p)

NonNegative : Pred ℚᵘ 0ℓ
NonNegative p = ℤ.NonNegative (↥ p)

-- Constructors

-- Note: these could be proved more elegantly using the constructors
-- from ℤ but it requires importing `Data.Integer.Properties` which
-- we would like to avoid doing.

≢-nonZero : ∀ {p} → p ≠ 0ℚᵘ → NonZero p
≢-nonZero {mkℚᵘ -[1+ _ ] _      } _   = _
≢-nonZero {mkℚᵘ +[1+ _ ] _      } _   = _
≢-nonZero {mkℚᵘ +0       zero   } p≢0 = p≢0 (*≡* refl)
≢-nonZero {mkℚᵘ +0       (suc d)} p≢0 = p≢0 (*≡* refl)

>-nonZero : ∀ {p} → p > 0ℚᵘ → NonZero p
>-nonZero {mkℚᵘ +0       _} (*<* (+<+ ()))
>-nonZero {mkℚᵘ +[1+ n ] _} (*<* _) = _

<-nonZero : ∀ {p} → p < 0ℚᵘ → NonZero p
<-nonZero {mkℚᵘ +[1+ n ] _} (*<* _) = _
<-nonZero {mkℚᵘ +0 _}       (*<* (+<+ ()))
<-nonZero {mkℚᵘ -[1+ n ] _} (*<* _) = _

positive : ∀ {p} → p > 0ℚᵘ → Positive p
positive {mkℚᵘ +[1+ n ]   _} (*<* _) = _
positive {mkℚᵘ +0         _} (*<* (+<+ ()))
positive {mkℚᵘ (-[1+_] n) _} (*<* ())

negative : ∀ {p} → p < 0ℚᵘ → Negative p
negative {mkℚᵘ +[1+ n ]   _} (*<* (+<+ ()))
negative {mkℚᵘ +0         _} (*<* (+<+ ()))
negative {mkℚᵘ (-[1+_] n) _} (*<* _       ) = _

nonPositive : ∀ {p} → p ≤ 0ℚᵘ → NonPositive p
nonPositive {mkℚᵘ +[1+ n ] _} (*≤* (+≤+ ()))
nonPositive {mkℚᵘ +0       _} (*≤* _) = _
nonPositive {mkℚᵘ -[1+ n ] _} (*≤* _) = _

nonNegative : ∀ {p} → p ≥ 0ℚᵘ → NonNegative p
nonNegative {mkℚᵘ +0       _} (*≤* _) = _
nonNegative {mkℚᵘ +[1+ n ] _} (*≤* _) = _
