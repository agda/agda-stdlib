------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsafe functions on primality
------------------------------------------------------------------------

module Unsafe.Data.Nat.Primality where

open import Data.Nat.Primality public

open import Data.Empty
open import Data.Fin as Fin hiding (_+_)
open import Data.Fin.Dec
open import Data.Nat
open import Unsafe.Data.Nat.Divisibility
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Relation.Unary

-- Decision procedure for primality.

prime? : Decidable Prime
prime? 0             = no λ()
prime? 1             = no λ()
prime? (suc (suc n)) = all? λ _ → ¬? (_ ∣? _)

private

  -- Example: 2 is prime.

  2-is-prime : Prime 2
  2-is-prime = from-yes (prime? 2)
