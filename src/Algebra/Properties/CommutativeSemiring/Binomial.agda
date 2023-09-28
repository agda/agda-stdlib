------------------------------------------------------------------------
-- The Agda standard library
--
-- The Binomial Theorem for Commutative Semirings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles
  using (CommutativeSemiring)

module Algebra.Properties.CommutativeSemiring.Binomial {a ℓ} (S : CommutativeSemiring a ℓ) where

open CommutativeSemiring S
open import Algebra.Properties.Semiring.Exp semiring using (_^_)
import Algebra.Properties.Semiring.Binomial semiring as Binomial
open Binomial public hiding (theorem)

------------------------------------------------------------------------
-- Here it is

theorem : ∀ n x y → (x + y) ^ n ≈ binomialExpansion x y n
theorem n x y = Binomial.theorem x y (*-comm x y) n

