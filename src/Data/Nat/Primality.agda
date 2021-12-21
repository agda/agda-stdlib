------------------------------------------------------------------------
-- The Agda standard library
--
-- Primality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Primality where

open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Properties using (all?; any?)
open import Data.Nat.Base using (ℕ; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Divisibility using (_∣_; _∤_; _∣?_)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Nullary.Negation using (¬?; decidable-stable)
open import Relation.Unary using (Decidable)

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

private

  -- Example: 2 is prime.

  2-is-prime : Prime 2
  2-is-prime = from-yes (prime? 2)

  -- Example: 6 is composite
  6-is-composite : Composite 6
  6-is-composite = from-yes (composite? 6)
