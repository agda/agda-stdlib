------------------------------------------------------------------------
-- The Agda standard library
--
-- Universe levels
------------------------------------------------------------------------

module Level where

-- Levels.

open import Agda.Builtin.Nat
open import Agda.Primitive as Prim public
  using    (Level; _⊔_)
  renaming (lzero to zero; lsuc to suc)

-- Increase a Level by a number of sucs.

_ℕ+_ : Nat → Level → Level
zero  ℕ+ ℓ = ℓ
suc n ℕ+ ℓ = Prim.lsuc (n ℕ+ ℓ)

-- Nat-computed Level.

infix 10 #_

#_ : Nat → Level
#_ = _ℕ+ Prim.lzero

-- Lifting.

record Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public
