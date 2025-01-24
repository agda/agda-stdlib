------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semiring.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (IntegralSemiring)

module Algebra.Properties.IntegralSemiring
  {a ℓ} (R : IntegralSemiring a ℓ)
  where

open import Algebra.Consequences.Base using (noZeroDivisors⇒x≉0∧y≉0⇒xẏ≉0)
import Algebra.Properties.Semiring.Triviality as Triviality
open import Data.Sum.Base using (inj₁; inj₂)

open IntegralSemiring R renaming (Carrier to A)
open Triviality semiring using (trivial⇒x≈0)

private
  variable
    x y : A


------------------------------------------------------------------------
-- Properties of Integral

x≉0∧y≉0⇒xẏ≉0 :  x ≉ 0# → y ≉ 0# → x * y ≉ 0#
x≉0∧y≉0⇒xẏ≉0 {x = x} x≉0 y≉0 xy≈0 with integral
... | inj₁ trivial        = x≉0 (trivial⇒x≈0 trivial x)
... | inj₂ noZeroDivisors = noZeroDivisors⇒x≉0∧y≉0⇒xẏ≉0 _≈_ noZeroDivisors x≉0 y≉0 xy≈0

