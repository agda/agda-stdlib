------------------------------------------------------------------------
-- The Agda standard library
--
-- Combinatorics operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Bool using (true; false)
open import Data.Nat.Base
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Nat.Factorial
open import Relation.Nullary using (yes; no; does)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)

module Data.Nat.Combinatorics.Base where

private
  _!≢0 : ∀ n → False (n ! ≟ 0)
  n !≢0 = fromWitnessFalse (n!≢0 n)

------------------------------------------------------------------------
-- Permutations / falling factorial

-- The number of ways, including order, that k objects can be chosen
-- from among n objects.

-- n P k = n ! / (n ∸ k) !

-- Base definition. Only valid for k ≤ n.

_P′_ : ℕ → ℕ → ℕ
n P′ zero    = 1
n P′ (suc k) = (n ∸ k) * (n P′ k)

-- Main definition. Valid for all k as deals with boundary case.

_P_ : ℕ → ℕ → ℕ
n P k with k ≤ᵇ n
... | false = 0
... | true  = n P′ k

------------------------------------------------------------------------
-- Combinations / binomial coefficient

-- The number of ways, disregarding order, that k objects can be chosen
-- from among n objects.

-- n C k = n ! / (k ! * (n ∸ k) !)

-- Base definition. Only valid for k ≤ n.

_C′_ : ℕ → ℕ → ℕ
n C′ k = ((n P′ k) / k !) {k !≢0}

-- Main definition. Valid for all k.
-- Deals with boundary case and exploits symmetry to improve performance.

_C_ : ℕ → ℕ → ℕ
n C k with k ≤ᵇ n
... | false = 0
... | true  = n C′ (k ⊓ (n ∸ k))
