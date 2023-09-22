------------------------------------------------------------------------
-- The Agda standard library
--
-- Null instance for ℕ
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Relation.Unary.Null where

open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _>_; z<s)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Unary using (Pred)
open import Relation.Unary.Null

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Instance

instance

  nullℕ : Null ℕ
  nullℕ = record { null = _≡ᵇ 0 }

NonZero : Pred ℕ _
NonZero = NonNull

------------------------------------------------------------------------
-- Simple predicates

-- Instances

instance
  nonZero : NonZero (suc n)
  nonZero = _

-- Constructors

≢-nonZero : n ≢ 0 → NonZero n
≢-nonZero {n = zero}  0≢0 = contradiction refl 0≢0
≢-nonZero {n = suc _} n≢0 = _

>-nonZero : n > 0 → NonZero n
>-nonZero z<s = _

-- Destructors

≢-nonZero⁻¹ : ∀ n → .{{NonZero n}} → n ≢ 0
≢-nonZero⁻¹ (suc n) ()

>-nonZero⁻¹ : ∀ n → .{{NonZero n}} → n > 0
>-nonZero⁻¹ (suc n) = z<s

------------------------------------------------------------------------
-- Specimen reimplementation

open import Agda.Builtin.Nat
  using (div-helper; mod-helper)

-- Division
-- Note properties of these are in `Nat.DivMod` not `Nat.Properties`

_/_ : (dividend divisor : ℕ) → .{{NonZero divisor}} → ℕ
m / n@(suc n-1) = div-helper 0 n-1 m n-1

-- Remainder/modulus
-- Note properties of these are in `Nat.DivMod` not `Nat.Properties`

_%_ : (dividend divisor : ℕ) → .{{NonZero divisor}} → ℕ
m % n@(suc n-1) = mod-helper 0 n-1 m n-1
