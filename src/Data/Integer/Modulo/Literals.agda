------------------------------------------------------------------------
-- The Agda standard library
--
-- Literals for integers mod n
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; NonTrivial)

module Data.Integer.Modulo.Literals n .{{_ : NonTrivial n}} where

open import Agda.Builtin.FromNat using (Number)
open import Data.Unit.Base using (⊤)
open import Data.Integer.Modulo using (ℤmod; fromℕ)

------------------------------------------------------------------------
-- Definitions

Constraint : ℕ → Set
Constraint _ = ⊤

fromNat : ∀ m → {{Constraint m}} → ℤmod n
fromNat m = fromℕ n m

number : Number (ℤmod n)
number = record { Constraint = Constraint ; fromNat = fromNat }
