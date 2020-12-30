------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the Greatest Common Divisor over semirings.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semiring)
import Algebra.Properties.Monoid.Divisibility as MonoidDiv
open import Data.Product using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

module Algebra.Properties.Semiring.GCD {a ℓ} (R : Semiring a ℓ) where

open Semiring R
open import Algebra.Properties.Semiring.Divisibility R

------------------------------------------------------------------------
-- Re-exporting definition of GCD

open import Algebra.Divisibility _≈_ _*_ public
  using (IsGCD; gcdᶜ)

------------------------------------------------------------------------
-- Properties of GCD

x≉0⊎y≉0⇒gcd≉0 : ∀ {x y d} → IsGCD x y d → x ≉ 0# ⊎ y ≉ 0# → d ≉ 0#
x≉0⊎y≉0⇒gcd≉0 (gcdᶜ d∣x _ _) (inj₁ x≉0) = x∣y∧y≉0⇒x≉0 d∣x x≉0
x≉0⊎y≉0⇒gcd≉0 (gcdᶜ _ d∣y _) (inj₂ y≉0) = x∣y∧y≉0⇒x≉0 d∣y y≉0
