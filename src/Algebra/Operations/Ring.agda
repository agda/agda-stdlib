------------------------------------------------------------------------
-- The Agda standard library
--
-- This module is DEPRECATED.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Operations.Ring
  {ℓ₁ ℓ₂} (ring : RawRing ℓ₁ ℓ₂)
  where

{-# WARNING_ON_IMPORT
"Algebra.Operations.Ring was deprecated in v1.5.
Use Algebra.Properties.Semiring.Exp(.TCOptimised) instead."
#-}

open import Data.Nat.Base as ℕ using (ℕ; suc; zero)

open RawRing ring

infixr 8 _^_+1
_^_+1 : Carrier → ℕ → Carrier
x ^ zero  +1 = x
x ^ suc n +1 = (x ^ n +1) * x

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero  = 1#
x ^ suc i = x ^ i +1
{-# INLINE _^_ #-}
