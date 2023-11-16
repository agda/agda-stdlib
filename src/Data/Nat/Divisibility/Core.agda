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

open import Data.Nat.Base using (ℕ; _*_; _<_; NonTrivial)
open import Data.Nat.Properties
open import Level using (0ℓ)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong₂; module ≡-Reasoning)
   
------------------------------------------------------------------------
-- Main definition
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
open _∣_ using (quotient) public

_∤_ : Rel ℕ 0ℓ
m ∤ n = ¬ (m ∣ n)

-- Smart constructor

pattern divides-refl q = divides q refl

------------------------------------------------------------------------
-- Restricted divisor relation

-- Relation for having a non-trivial divisor below a given bound.
-- Useful when reasoning about primality.
record _BoundedNonTrivialDivisor_ (m n : ℕ) : Set where
  constructor boundedNonTrivialDivisor
  field
    {divisor}       : ℕ
    .{{nontrivial}} : NonTrivial divisor
    divisor-<       : divisor < m
    divisor-∣       : divisor ∣ n

------------------------------------------------------------------------
-- Basic properties

*-pres-∣ : ∀ {m n o p} → o ∣ m → p ∣ n → o * p ∣ m * n
*-pres-∣ {m} {n} {o} {p} (divides c m≡c*o) (divides d n≡d*p) =
  divides (c * d) (begin
    m * n             ≡⟨ cong₂ _*_ m≡c*o n≡d*p ⟩
    (c * o) * (d * p) ≡⟨ [m*n]*[o*p]≡[m*o]*[n*p] c o d p ⟩
    (c * d) * (o * p) ∎)
  where open ≡-Reasoning
