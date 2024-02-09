------------------------------------------------------------------------
-- The Agda standard library
--
-- Literals for bounded natural numbers ℕ<
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base as ℕ using (ℕ)

module Data.Nat.Bounded.Literals (n : ℕ) where

open import Agda.Builtin.FromNat using (Number)
open import Data.Bool.Base using (T)
import Data.Nat.Properties as ℕ

open import Data.Nat.Bounded using (ℕ<; ⟦_⟧<_)

------------------------------------------------------------------------
-- Literals

Constraint : ℕ → Set
Constraint m = T (m ℕ.<ᵇ n)

fromNat : ∀ m → {{Constraint m}} → ℕ< n
fromNat m {{lt}} = ⟦ m ⟧< ℕ.<ᵇ⇒< m n lt

number : Number (ℕ< n)
number = record { Constraint = Constraint ; fromNat = fromNat }
