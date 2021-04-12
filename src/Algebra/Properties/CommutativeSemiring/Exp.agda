------------------------------------------------------------------------
-- The Agda standard library
--
-- Exponentiation defined over a commutative semiring as repeated multiplication
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.CommutativeSemiring.Exp
  {a ℓ} (S : CommutativeSemiring a ℓ) where

open CommutativeSemiring S
import Algebra.Properties.CommutativeMonoid.Mult *-commutativeMonoid as Mult

------------------------------------------------------------------------
-- Definition

open import Algebra.Properties.Semiring.Exp semiring public

------------------------------------------------------------------------
-- Properties

^-distrib-* : ∀ x y n → (x * y) ^ n ≈ x ^ n * y ^ n
^-distrib-* = Mult.×-distrib-+
