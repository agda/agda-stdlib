------------------------------------------------------------------------
-- The Agda standard library
--
-- Primality
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Primality where

open import Data.Empty using (⊥)
open import Data.Nat.Base
open import Data.Nat.Divisibility
open import Data.Nat.GCD using (module GCD; module Bézout)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (flip; _∘_; _∘′_)
open import Relation.Nullary.Decidable as Dec
  using (yes; no; from-yes; ¬?; decidable-stable; _×-dec_; _→-dec_)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality
  using (refl; sym; cong; subst)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Definitions

-- Definition of compositeness

Composite : ℕ → Set
Composite 0 = ⊥
Composite 1 = ⊥
Composite n = ∃ λ d → 2 ≤ d × d < n × d ∣ n

-- Definition of primality.

Prime : ℕ → Set
Prime 0 = ⊥
Prime 1 = ⊥
Prime n = ∀ {d} → 2 ≤ d → d < n → d ∤ n

------------------------------------------------------------------------
-- Decidability

composite? : Decidable Composite
composite? 0               = no λ()
composite? 1               = no λ()
composite? n@(suc (suc _)) = Dec.map′
  (map₂ λ { (a , b , c) → (b , a , c)})
  (map₂ λ { (a , b , c) → (b , a , c)})
  (anyUpTo? (λ d → 2 ≤? d ×-dec d ∣? n) n)

prime? : Decidable Prime
prime? 0               = no λ()
prime? 1               = no λ()
prime? n@(suc (suc _)) = Dec.map′
  (λ f {d} → flip (f {d}))
  (λ f {d} → flip (f {d}))
  (allUpTo? (λ d → 2 ≤? d →-dec ¬? (d ∣? n)) n)

------------------------------------------------------------------------
-- Relationships between compositeness and primality

composite⇒¬prime : Composite n → ¬ Prime n
composite⇒¬prime {n@(suc (suc _))} (d , 2≤d , d<n , d∣n) n-prime =
  n-prime 2≤d d<n d∣n

¬composite⇒prime : 2 ≤ n → ¬ Composite n → Prime n
¬composite⇒prime (s≤s (s≤s _)) ¬n-composite {d} 2≤d d<n d∣n =
  ¬n-composite (d , 2≤d , d<n , d∣n)

prime⇒¬composite : Prime n → ¬ Composite n
prime⇒¬composite {n@(suc (suc _))} n-prime (d , 2≤d , d<n , d∣n) =
  n-prime 2≤d d<n d∣n

-- note that this has to recompute the factor!
¬prime⇒composite : 2 ≤ n → ¬ Prime n → Composite n
¬prime⇒composite {n} 2≤n ¬n-prime =
  decidable-stable (composite? n) (¬n-prime ∘′ ¬composite⇒prime 2≤n)

------------------------------------------------------------------------
-- Euclid's lemma

-- For p prime, if p ∣ m * n, then either p ∣ m or p ∣ n.
-- This demonstrates that the usual definition of prime numbers matches the
-- ring theoretic definition of a prime element of the semiring ℕ.
-- This is useful for proving many other theorems involving prime numbers.
euclidsLemma : ∀ m n {p} → Prime p → p ∣ m * n → p ∣ m ⊎ p ∣ n
euclidsLemma m n {p@(suc (suc _))} p-prime p∣m*n = result
  where
  open ∣-Reasoning

  p∣rmn : ∀ r → p ∣ r * m * n
  p∣rmn r = begin
    p           ∣⟨ p∣m*n ⟩
    m * n       ∣⟨ n∣m*n r ⟩
    r * (m * n) ≡˘⟨ *-assoc r m n ⟩
    r * m * n   ∎

  result : p ∣ m ⊎ p ∣ n
  result with Bézout.lemma m p
  -- if the GCD of m and p is zero then p must be zero, which is impossible as p
  -- is a prime
  ... | Bézout.result 0 g _ = contradiction (0∣⇒≡0 (GCD.gcd∣n g)) λ()

  -- if the GCD of m and p is one then m and p is coprime, and we know that for
  -- some integers s and r, sm + rp = 1. We can use this fact to determine that p
  -- divides n
  ... | Bézout.result 1 _ (Bézout.+- r s 1+sp≡rm) =
    inj₂ (flip ∣m+n∣m⇒∣n (n∣m*n*o s n) (begin
      p             ∣⟨ p∣rmn r ⟩
      r * m * n     ≡˘⟨ cong (_* n) 1+sp≡rm ⟩
      n + s * p * n ≡⟨ +-comm n (s * p * n) ⟩
      s * p * n + n ∎))

  ... | Bézout.result 1 _ (Bézout.-+ r s 1+rm≡sp) =
    inj₂ (flip ∣m+n∣m⇒∣n (p∣rmn r) (begin
      p             ∣⟨ n∣m*n*o s n ⟩
      s * p * n     ≡˘⟨ cong (_* n) 1+rm≡sp ⟩
      n + r * m * n ≡⟨ +-comm n (r * m * n) ⟩
      r * m * n + n ∎))

  -- if the GCD of m and p is greater than one, then it must be p and hence p ∣ m.
  ... | Bézout.result d@(suc (suc _)) g _ with d ≟ p
  ...   | yes refl = inj₁ (GCD.gcd∣m g)
  ...   | no  d≢p  = contradiction (GCD.gcd∣n g) (p-prime 2≤d d<p)
    where 2≤d = s≤s (s≤s z≤n); d<p = flip ≤∧≢⇒< d≢p (∣⇒≤ (GCD.gcd∣n g))

private

  -- Example: 2 is prime.
  2-is-prime : Prime 2
  2-is-prime = from-yes (prime? 2)


  -- Example: 6 is composite
  6-is-composite : Composite 6
  6-is-composite = from-yes (composite? 6)
