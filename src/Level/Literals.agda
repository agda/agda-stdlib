------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion from naturals to universe levels
------------------------------------------------------------------------

module Level.Literals where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.FromNat
open import Agda.Builtin.Unit
open import Level using (Level; 0ℓ)

-- Increase a Level by a number of sucs.

_ℕ+_ : ℕ → Level → Level
zero  ℕ+ ℓ = ℓ
suc n ℕ+ ℓ = Level.suc (n ℕ+ ℓ)

-- Nat-computed Level.

infix 10 #_

#_ : ℕ → Level
#_ = _ℕ+ 0ℓ

-- Literal overloading for levels.

Levelℕ : Number Level
Levelℕ .Number.Constraint _ = ⊤
Levelℕ .Number.fromNat    n = # n
