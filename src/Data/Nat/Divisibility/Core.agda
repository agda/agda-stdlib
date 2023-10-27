------------------------------------------------------------------------
-- The Agda standard library
--
-- Core definition of divisibility
------------------------------------------------------------------------

-- The definition of divisibility is split out from
-- `Data.Nat.Divisibility` to avoid a dependency cycle with
-- `Data.Nat.DivMod`.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Divisibility.Core where

open import Data.Nat.Base using (ℕ; _*_; NonZero; ≢-nonZero; ≢-nonZero⁻¹; _<_)
open import Data.Nat.Properties
open import Level using (0ℓ)
open import Relation.Nullary.Negation using (¬_; contraposition)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; module ≡-Reasoning)

------------------------------------------------------------------------
-- Definition
--
-- m ∣ n is inhabited iff m divides n. Some sources, like Hardy and
-- Wright's "An Introduction to the Theory of Numbers", require m to
-- be non-zero. However, some things become a bit nicer if m is
-- allowed to be zero. For instance, _∣_ becomes a partial order, and
-- the gcd of 0 and 0 becomes defined.

infix 4 _∣_ _∤_

record _∣_ (m n : ℕ) : Set where
  constructor divides
  field quotient : ℕ
        equality : n ≡ quotient * m

  quotient≢0 : .{{NonZero n}} → NonZero quotient
  quotient≢0 rewrite equality = m*n≢0⇒m≢0 quotient

  n≡m*quotient : n ≡ m * quotient
  n≡m*quotient rewrite equality = *-comm quotient m

  quotient>1 :  (m<n : m < n) → 1 < quotient
  quotient>1 m<n = ≰⇒> λ q≤1 → n≮n n (begin-strict
      n            ≡⟨ equality ⟩
      quotient * m ≤⟨ *-monoˡ-≤ m q≤1 ⟩
      1 * m        ≡⟨ *-identityˡ m ⟩
      m            <⟨ m<n ⟩
      n            ∎) where open ≤-Reasoning

  quotient< : (1<m : 1 < m) .{{_ : NonZero n}} → quotient < n
  quotient< 1<m = begin-strict
    quotient     <⟨ m<m*n quotient m 1<m ⟩
    quotient * m ≡⟨ equality ⟨
    n            ∎ where open ≤-Reasoning; instance _ = quotient≢0


_∤_ : Rel ℕ 0ℓ
m ∤ n = ¬ (m ∣ n)

-- smart constructor

pattern divides-refl q = divides q refl

-- smart destructor

module _ {m n} (m∣n : m ∣ n) (open _∣_ m∣n using (quotient; n≡m*quotient)) where

  quotient∣ : quotient ∣ n
  quotient∣ = divides m n≡m*quotient

-- exports

open _∣_ using (quotient; quotient≢0; quotient>1; quotient<) public

------------------------------------------------------------------------
-- Basic properties

*-pres-∣ : ∀ {m n o p} → o ∣ m → p ∣ n → o * p ∣ m * n
*-pres-∣ {m} {n} {o} {p} (divides c m≡c*o) (divides d n≡d*p) =
  divides (c * d) (begin
    m * n             ≡⟨ cong₂ _*_ m≡c*o n≡d*p ⟩
    (c * o) * (d * p) ≡⟨ [m*n]*[o*p]≡[m*o]*[n*p] c o d p ⟩
    (c * d) * (o * p) ∎)
  where open ≡-Reasoning
