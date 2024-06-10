------------------------------------------------------------------------
-- The Agda standard library
--
-- Algebra Literals, from a SuccessorSet
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (SuccessorSet)

module Algebra.Literals {c ℓ} (successorSet : SuccessorSet c ℓ) where

open import Agda.Builtin.FromNat using (Number)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Unit.Polymorphic.Base

open SuccessorSet successorSet


------------------------------------------------------------------------
-- Number instance

fromℕ : (n : ℕ) → Carrier
fromℕ zero    = zero#
fromℕ (suc n) = suc# (fromℕ n)

instance
  number : Number Carrier
  number = record { Constraint = λ _ → ⊤ ; fromNat = λ n → fromℕ n }
