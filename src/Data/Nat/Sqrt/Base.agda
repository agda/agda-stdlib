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

open import Data.Bool.Base
open import Data.Nat.Base

sqrt : ℕ → ℕ
sqrt zero    = zero
sqrt (suc n) = if (0 <ᵇ d) then √n else suc √n
  module Sqrt where

  √n = sqrt n

  a*a+b∸c : ℕ → ℕ → ℕ → ℕ
  a*a+b∸c zero    b c = b ∸ c
  a*a+b∸c (suc a) b c = a*a+b∸c a (suc (b + (a + a))) c

  d = a*a+b∸c √n (√n + √n) n
