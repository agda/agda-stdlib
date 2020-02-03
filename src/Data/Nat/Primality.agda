------------------------------------------------------------------------
-- The Agda standard library
--
-- Primality
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Primality where

open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Fin.Properties using (all?)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Nat.Divisibility using (_∤_; _∣?_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (from-yes)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Unary using (Decidable)

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

private

  -- Example: 2 is prime.

  2-is-prime : Prime 2
  2-is-prime = from-yes (prime? 2)
