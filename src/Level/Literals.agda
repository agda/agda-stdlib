------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion from naturals to universe levels
------------------------------------------------------------------------

module Level.Literals where

open import Agda.Builtin.Nat
open import Agda.Builtin.FromNat
open import Agda.Builtin.Unit
open import Level using (Level)

-- Increase a Level by a number of sucs.

_ℕ+_ : Nat → Level → Level
zero  ℕ+ ℓ = ℓ
suc n ℕ+ ℓ = Level.suc (n ℕ+ ℓ)

-- Nat-computed Level.

infix 10 #_

#_ : Nat → Level
#_ = _ℕ+ Level.zero

-- Literal overloading for levels.

LevelNat : Number Level
LevelNat .Number.Constraint _ = ⊤
LevelNat .Number.fromNat    n = # n
