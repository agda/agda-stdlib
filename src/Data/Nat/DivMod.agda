------------------------------------------------------------------------
-- The Agda standard library
--
-- Integer division
------------------------------------------------------------------------

module Data.Nat.DivMod where

open import Data.Fin as Fin using (Fin; toℕ)
open import Data.Nat.Base
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Agda.Builtin.Nat using ( div-helper )

infixl 7 _div_

-- A specification of integer division.

record DivMod (dividend divisor : ℕ) : Set where
  constructor result
  field
    quotient  : ℕ
    remainder : Fin divisor
    property  : dividend ≡ toℕ remainder + quotient * divisor

-- Integer division.

_div_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
(d div 0) {}
(d div suc s) = div-helper 0 s d s

