------------------------------------------------------------------------
-- The Agda standard library
--
-- Core definitions for standalone, structurally inductive binomial
-- expansions over natural numbers.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Binomial.Base where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _^_)

------------------------------------------------------------------------
-- Pascal's Combinatorics

-- Binomial coefficient (n choose k). Defined via Pascal's triangle
-- recurrence for direct structural induction.
infixl 6 _C_
_C_ : ℕ → ℕ → ℕ
n C zero = 1
zero C (suc k) = 0
(suc n) C (suc k) = (n C k) + (n C (suc k))

------------------------------------------------------------------------
-- Discrete Summation

-- The i-th term of the binomial expansion: (k choose i) * n^i.
term : ℕ → ℕ → ℕ → ℕ
term n k i = (k C i) * (n ^ i)

-- The i-th term multiplied by n: (k choose i) * n^(i+1).
termSuc : ℕ → ℕ → ℕ → ℕ
termSuc n k i = (k C i) * (n ^ suc i)

-- The sum of the first m terms of the binomial expansion.
sumBinomial : ℕ → ℕ → ℕ → ℕ
sumBinomial n k zero = term n k zero
sumBinomial n k (suc m) = term n k (suc m) + sumBinomial n k m

-- The sum of the first m terms of the binomial expansion, multiplied by n.
sumBinomialSuc : ℕ → ℕ → ℕ → ℕ
sumBinomialSuc n k zero = termSuc n k zero
sumBinomialSuc n k (suc m) = termSuc n k (suc m) + sumBinomialSuc n k m
