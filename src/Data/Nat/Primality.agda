------------------------------------------------------------------------
-- The Agda standard library
--
-- Primality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Primality where

open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (all?; any?; toℕ-fromℕ<)
open import Data.Nat.Base using (ℕ; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Divisibility using (_∣_; _∤_; _∣?_; ∣⇒≤; 0∣⇒≡0; ∣m+n∣m⇒∣n; m∣m*n; n∣m*n; module ∣-Reasoning)
open import Data.Nat.GCD using (module GCD; module Bézout)
open import Data.Nat.Properties using (_≟_; ≤∧≢⇒<; +-comm; *-assoc; +-cancelˡ-≤)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Nullary.Negation using (¬?; contradiction; decidable-stable)
open import Relation.Unary using (Decidable)
open import Relation.Binary.PropositionalEquality using (sym; cong; subst)

-- Definition of compositeness

Composite : ℕ → Set
Composite 0 = ⊥
Composite 1 = ⊥
Composite (suc (suc n)) = Σ[ i ∈ Fin n ] 2 + toℕ i ∣ 2 + n

-- Decision procedure for compositeness

composite? : Decidable Composite
composite? 0 = no λ()
composite? 1 = no λ()
composite? (suc (suc n)) = any? (λ _ → _ ∣? _)

-- Definition of primality.

Prime : ℕ → Set
Prime 0             = ⊥
Prime 1             = ⊥
Prime (suc (suc n)) = (i : Fin n) → 2 + toℕ i ∤ 2 + n

-- Decision procedure for primality.

prime? : Decidable Prime
prime? 0             = no λ()
prime? 1             = no λ()
prime? (suc (suc n)) = all? (λ _ → ¬? (_ ∣? _))

-- Relation between compositeness and primality

composite⇒¬prime : ∀ {n} → Composite n → ¬ Prime n
composite⇒¬prime {suc (suc n)} (i , 2+i∣2+n) 2+n-prime = 2+n-prime i 2+i∣2+n

¬composite⇒prime : ∀ {n} → 2 ≤ n → ¬ Composite n → Prime n
¬composite⇒prime {suc (suc n)} (s≤s (s≤s _)) ¬n-composite i 2+i∣2+n = ¬n-composite (i , 2+i∣2+n)

prime⇒¬composite : ∀ {n} → Prime n → ¬ Composite n
prime⇒¬composite {suc (suc n)} 2+n-prime (i , 2+i∣2+n) = 2+n-prime i 2+i∣2+n

-- note that this has to recompute the factor!
¬prime⇒composite : ∀ {n} → 2 ≤ n → ¬ Prime n → Composite n
¬prime⇒composite {n} 2≤n ¬n-prime = decidable-stable (composite? n) λ ¬n-composite → ¬n-prime (¬composite⇒prime 2≤n ¬n-composite)

-- For p prime, if p ∣ m * n, then either p ∣ m or p ∣ n.
-- This demonstrates that the usual definition of prime numbers matches the
-- ring theoretic definition of a prime element of the semiring ℕ.
-- This is useful for proving many other theorems involving prime numbers.
euclid'sLemma : ∀ m n {p} → Prime p → p ∣ m * n → p ∣ m ⊎ p ∣ n
euclid'sLemma m n {p} p-prime p∣m*n with Bézout.lemma m p
-- if the GCD of m and p is zero then p must be zero, which is impossible as p
-- is a prime
... | Bézout.result 0 g _ = contradiction p-prime (subst Prime (0∣⇒≡0 (proj₂ (GCD.commonDivisor g))))
-- if the GCD of m and p is one then m and p is coprime, and we know that for
-- some integers s and r, sm + rp = 1. We can use this fact to determine that p
-- divides n
... | Bézout.result 1 _ (Bézout.+- r s 1+sp≡rm) = inj₂ (∣m+n∣m⇒∣n p∣spn+n p∣spn)
  where
    open ∣-Reasoning
    p∣spn+n : p ∣ s * p * n + n
    p∣spn+n = begin
      p             ∣⟨ p∣m*n ⟩
      m * n         ∣⟨ n∣m*n r ⟩
      r * (m * n)   ≡˘⟨ *-assoc r m n ⟩
      r * m * n     ≡˘⟨ cong (_* n) 1+sp≡rm ⟩
      n + s * p * n ≡⟨ +-comm n (s * p * n) ⟩
      s * p * n + n ∎
    p∣spn : p ∣ s * p * n
    p∣spn = begin
      p         ∣⟨ n∣m*n s ⟩
      s * p     ∣⟨ m∣m*n n ⟩
      s * p * n ∎
... | Bézout.result 1 _ (Bézout.-+ r s 1+rm≡sp) = inj₂ (∣m+n∣m⇒∣n p∣rmn+n p∣rmn)
  where
    open ∣-Reasoning
    p∣rmn+n : p ∣ r * m * n + n
    p∣rmn+n = begin
      p             ∣⟨ n∣m*n s ⟩
      s * p         ∣⟨ m∣m*n n ⟩
      s * p * n     ≡˘⟨ cong (_* n) 1+rm≡sp ⟩
      n + r * m * n ≡⟨ +-comm n (r * m * n) ⟩
      r * m * n + n ∎
    p∣rmn : p ∣ r * m * n
    p∣rmn = begin
      p           ∣⟨ p∣m*n ⟩
      m * n       ∣⟨ n∣m*n r ⟩
      r * (m * n) ≡˘⟨ *-assoc r m n ⟩
      r * m * n   ∎
-- if the GCD of m and p is greater than one, then it must be p and hence p ∣ m.
-- Proving this is a little messy, though!
... | Bézout.result (suc (suc n)) g _ with suc (suc n) ≟ p
... | yes 2+n=p = inj₁ (subst (_∣ m) 2+n=p (proj₁ (GCD.commonDivisor g)))
... | no  2+n≠p with p
... | suc (suc p′)
  = contradiction
    (subst (λ n′ → 2 + n′ ∣ 2 + p′) (sym (toℕ-fromℕ< _)) (proj₂ (GCD.commonDivisor g)))
    (p-prime (fromℕ< (+-cancelˡ-≤ 2 (≤∧≢⇒< (∣⇒≤ (proj₂ (GCD.commonDivisor g))) 2+n≠p))))

private

  -- Example: 2 is prime.

  2-is-prime : Prime 2
  2-is-prime = from-yes (prime? 2)

  -- Example: 6 is composite
  6-is-composite : Composite 6
  6-is-composite = from-yes (composite? 6)
