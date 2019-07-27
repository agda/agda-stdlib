------------------------------------------------------------------------
-- The Agda standard library
--
-- Simple predicates over ℕ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Predicate where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Definition

-- The predicates here are defined in a slight odd manner. Instead of
-- defining `NonZero x` as `x ≢ 0` or via a datatype as might be
-- expected we define it in terms of `False` and the decidability of
-- propositional equality `_≟_`. This ensures that for any `x` of the
-- form `suc y` then Agda can automatically infer `NonZero x` and
-- hence when it is passed as an implicit argument no proof is required.
-- See `Data.Nat.DivMod` for an example.

NonZero : Pred ℕ 0ℓ
NonZero x = False (x ≟ 0)

------------------------------------------------------------------------
-- Constructors

nonZero : ∀ {n} → n ≢ 0 → NonZero n
nonZero {zero}  0≢0 = 0≢0 refl
nonZero {suc n} n≢0 = _

nonZero< : ∀ {n} → 0 < n → NonZero n
nonZero< (s≤s 0<n) = _
