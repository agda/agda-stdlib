------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural number square root
--
-- Goodstein's (1957) primitive recursive definition, taken from
-- Troelstra and van Dalen, Constructivity in Mathematics, Vol. I
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Sqrt.Base where

open import Data.Bool.Base using (if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc; 2+; _+_; _∸_; _<ᵇ_)

sqrt : ℕ → ℕ
sqrt zero    = zero
sqrt (suc n) = if (0 <ᵇ d) then √n else suc √n
  module Sqrt where
  -- helper functions to compute d
  2*_ : ℕ → ℕ
  2* zero  = zero
  2* suc m = 2+ (2* m)
  _^2+2*_∸_ : ℕ → ℕ → ℕ → ℕ
  zero    ^2+2* n ∸ o = (2* n) ∸ o
  (suc m) ^2+2* n ∸ o = m ^2+2* (suc (m + n)) ∸ (suc o)
  -- then recur on n
  √n = sqrt n
  d = √n ^2+2* √n ∸ n

private
  open import Agda.Builtin.Equality using (_≡_; refl)

  test : sqrt 16 ≡ 4
  test = refl
