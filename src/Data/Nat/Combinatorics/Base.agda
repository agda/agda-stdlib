------------------------------------------------------------------------
-- The Agda standard library
--
-- Combinatorics operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Combinatorics.Base where

open import Data.Bool.Base using (if_then_else_)
open import Data.Nat.Base
open import Data.Nat.Properties using (_!≢0)

-- NOTE: These operators are not implemented as efficiently as they
-- could be. See the following link for more details.
--
-- https://math.stackexchange.com/questions/202554/how-do-i-compute-binomial-coefficients-efficiently

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
n P k = if k ≤ᵇ n then n P′ k else 0

------------------------------------------------------------------------
-- Combinations / binomial coefficient

-- The number of ways, disregarding order, that k objects can be chosen
-- from among n objects.

-- n C k = n ! / (k ! * (n ∸ k) !)

-- Base definition. Only valid for k ≤ n.

_C′_ : ℕ → ℕ → ℕ
n C′ k = (n P′ k) / k !
  where instance _ = k !≢0

-- Main definition. Valid for all k.
-- Deals with boundary case and exploits symmetry to improve performance.

_C_ : ℕ → ℕ → ℕ
n C k = if k ≤ᵇ n then n C′ (k ⊓ (n ∸ k)) else 0
