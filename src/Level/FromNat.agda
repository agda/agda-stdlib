------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion from naturals to universe levels
------------------------------------------------------------------------

module Level.FromNat where

open import Agda.Builtin.Nat
open import Level using (Level)

-- Increase a Level by a number of sucs.

_ℕ+_ : Nat → Level → Level
zero  ℕ+ ℓ = ℓ
suc n ℕ+ ℓ = Level.suc (n ℕ+ ℓ)

-- Nat-computed Level.

infix 10 #_

#_ : Nat → Level
#_ = _ℕ+ Level.zero
