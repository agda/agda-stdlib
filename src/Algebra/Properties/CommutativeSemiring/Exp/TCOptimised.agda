------------------------------------------------------------------------
-- The Agda standard library
--
-- Exponentiation over a semiring optimised for type-checking.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Nat.Base as ℕ using (zero; suc)
import Data.Nat.Properties as ℕ
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

module Algebra.Properties.CommutativeSemiring.Exp.TCOptimised
  {a ℓ} (S : CommutativeSemiring a ℓ) where

open CommutativeSemiring S
open import Relation.Binary.Reasoning.Setoid setoid

import Algebra.Properties.CommutativeMonoid.Mult.TCOptimised *-commutativeMonoid as Mult

------------------------------------------------------------------------
-- Re-export definition and properties for semirings

open import Algebra.Properties.Semiring.Exp.TCOptimised semiring public

------------------------------------------------------------------------
-- Properties

^-distrib-* : ∀ x y n → (x * y) ^ n ≈ x ^ n * y ^ n
^-distrib-* = Mult.×-distrib-+
