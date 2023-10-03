------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers whose prime factors are all above a bound
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Primality.Rough where

open import Data.Nat.Base using (ℕ; suc; _≤_; _<_; z≤n; s≤s; _+_)
open import Data.Nat.Divisibility using (_∣_; _∤_; ∣-trans; ∣1⇒≡1)
open import Data.Nat.Induction using (<-rec; <-Rec)
open import Data.Nat.Primality using (Prime; composite?)
open import Data.Nat.Properties using (_≟_; <-trans; ≤⇒≯; ≤∧≢⇒<; m<1+n⇒m<n∨m≡n)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (_∘_; flip)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality.Core using (refl)

private
  variable
    k m n : ℕ

-- A number is k-rough if all its prime factors are greater than or equal to k
_Rough_ : ℕ → ℕ → Set
k Rough n = ∀ {d} → 1 < d → d < k → d ∤ n

-- any number is 2-rough because all primes are greater than or equal to 2
2-rough-n : ∀ n → 2 Rough n
2-rough-n _ 1<d 2>d with () ← ≤⇒≯ 1<d 2>d

extend-∤ : k Rough n → k ∤ n → suc k Rough n
extend-∤ k-rough-n k∤n 1<d d<suc[k] with m<1+n⇒m<n∨m≡n d<suc[k]
... | inj₁ suc[d]≤k = k-rough-n 1<d suc[d]≤k
... | inj₂ refl = k∤n

-- 1 is always rough
k-rough-1 : ∀ k → k Rough 1
k-rough-1 k {d} 1<d d<k d∣1 with ∣1⇒≡1 d∣1
k-rough-1 k {.1} (s≤s ()) d<k d∣1 | refl

-- if a number is k-rough, then so are all of its divisors
reduce-∣ : k Rough m → n ∣ m → k Rough n
reduce-∣ k-rough-n n∣m d<k d-prime d∣n = k-rough-n d<k d-prime (∣-trans d∣n n∣m)

-- if a number is k-rough, and k divides it, then k must be prime
roughn∧∣n⇒prime : k Rough n → 2 ≤ k → k ∣ n → Prime k
roughn∧∣n⇒prime {k = suc (suc k)} {n = n} k-rough-n (s≤s (s≤s z≤n)) k∣n
  = <-rec (λ d → 2 ≤ d → d < 2 + k → d ∤ 2 + k) (roughn∧∣n⇒primeRec k-rough-n k∣n) _
  where
  roughn∧∣n⇒primeRec : ∀ {k} → k Rough n → k ∣ n → ∀ d → <-Rec (λ d′ → 2 ≤ d′ → d′ < k → d′ ∤ k) d → 2 ≤ d → d < k → d ∤ k
  roughn∧∣n⇒primeRec k-rough-n k∣n (suc (suc d)) rec (s≤s (s≤s z≤n)) d<k with composite? (2 + d)
  ... | yes (d′ , 2≤d′ , d′<d , d′∣d) = rec d′ d′<d 2≤d′ (<-trans d′<d d<k) ∘ ∣-trans d′∣d
  ... | no ¬d-composite = k-rough-n (s≤s (s≤s z≤n)) d<k ∘ flip ∣-trans k∣n
