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
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl)


private
  variable m n o p : ℕ

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

_∤_ : Rel ℕ _
m ∤ n = ¬ (m ∣ n)

-- Smart constructor

pattern divides-refl q = divides q refl

open _∣_ using (quotient) public

------------------------------------------------------------------------
-- Restricted divisor relation

-- Relation for having a non-trivial divisor below a given bound.
-- Useful when reasoning about primality.
infix 10 _HasNonTrivialDivisorLessThan_

record _HasNonTrivialDivisorLessThan_ (m n : ℕ) : Set where
  constructor hasNonTrivialDivisor
  field
    {divisor}       : ℕ
    .{{nontrivial}} : NonTrivial divisor
    divisor-<       : divisor < n
    divisor-∣       : divisor ∣ m

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.1

*-pres-∣ : o ∣ m → p ∣ n → o * p ∣ m * n
*-pres-∣ {o} {m@.(q * o)} {p} {n@.(r * p)} (divides-refl q) (divides-refl r) =
  divides (q * r) ([m*n]*[o*p]≡[m*o]*[n*p] q o r p)

{-# WARNING_ON_USAGE *-pres-∣
"Warning: *-pres-∣ was deprecated in v2.1.
 Please use Data.Nat.Divisibility.*-pres-∣ instead."
#-}
