------------------------------------------------------------------------
-- The Agda standard library
--
-- Some defined operations over Rings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- This module gives the definition of _^_ which is used throughout
-- the library. It's a little different from the normal definition:
--
--   x ^ zero  = 1#
--   x ^ suc i = x * x ^ i
--
-- This is for two reasons. First, we want to avoid unnecessarily
-- multiplying by 1# if possible:
--
--     Standard definition: x ^ 2 = x * x * 1#
--     Our definition:      x ^ 2 = x * x
--
-- This speeds up typechecking and makes for much more readable
-- proofs.
--
-- Secondly, we want to associate to the left:
--
--     Standard definition: x ^ 3 = x * (x * (x * 1#))
--     Our definition:      x ^ 2 = (x * x) * x
--
-- As counterintuitive as it may seem, this also speeds up
-- typechecking.

open import Algebra

module Algebra.Operations.Ring
  {ℓ₁ ℓ₂} (ring : RawRing ℓ₁ ℓ₂)
  where

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
