------------------------------------------------------------------------
-- The Agda standard library
--
-- Combinatorics operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Combinatorics where
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s; _+_; _*_)
open import Data.Nat.Properties using (*-mono-≤; module ≤-Reasoning; m≢0∧n≢0⇒m*n≢0; 1+n≢0)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary.Negation using (contradiction)

_! : ℕ → ℕ
zero ! = 1
suc n ! = (suc n) * n !

1≤n! : ∀ n → 1 ≤ n !
1≤n! zero = s≤s z≤n
1≤n! (suc n) = begin
  1                     ≡⟨⟩
  1 * 1                 ≤⟨ *-mono-≤ (s≤s (z≤n {n = n})) (1≤n! n) ⟩
  suc n * n !           ≡⟨⟩
  (suc n !)             ∎
  where
    open ≤-Reasoning

n!≢0 : ∀ n → n ! ≢ 0
n!≢0 zero ()
n!≢0 (suc n) n!≡0 = m≢0∧n≢0⇒m*n≢0 (1+n≢0 {n}) (n!≢0 n) n!≡0
