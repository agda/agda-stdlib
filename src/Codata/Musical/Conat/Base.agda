------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive "natural" numbers: base type and operations
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K --guardedness #-}

module Codata.Musical.Conat.Base where

open import Codata.Musical.Notation
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function.Base using (_∋_)

------------------------------------------------------------------------
-- The type

data Coℕ : Set where
  zero : Coℕ
  suc  : (n : ∞ Coℕ) → Coℕ

------------------------------------------------------------------------
-- Constant

∞ℕ : Coℕ
∞ℕ = suc (♯ ∞ℕ)

------------------------------------------------------------------------
-- Some operations

pred : Coℕ → Coℕ
pred zero    = zero
pred (suc n) = ♭ n

fromℕ : ℕ → Coℕ
fromℕ zero    = zero
fromℕ (suc n) = suc (♯ fromℕ n)

infixl 6 _+_

_+_ : Coℕ → Coℕ → Coℕ
zero  + n = n
suc m + n = suc (♯ (♭ m + n))
