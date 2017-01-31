------------------------------------------------------------------------
-- The Agda standard library
--
-- Primality
------------------------------------------------------------------------

module Data.Nat.Primality where

open import Data.Empty
open import Data.Fin as Fin hiding (_+_)
open import Data.Nat
open import Data.Nat.Divisibility
open import Relation.Nullary

-- Definition of primality.

Prime : ℕ → Set
Prime 0             = ⊥
Prime 1             = ⊥
Prime (suc (suc n)) = (i : Fin n) → ¬ (2 + Fin.toℕ i ∣ 2 + n)
