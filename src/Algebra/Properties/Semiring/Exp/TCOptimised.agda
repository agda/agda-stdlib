------------------------------------------------------------------------
-- The Agda standard library
--
-- Exponentiation over a semiring optimised for type-checking.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Nat.Base as ℕ using (zero; suc)
import Data.Nat.Properties as ℕ
open import Relation.Binary
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

module Algebra.Properties.Semiring.Exp.TCOptimised
  {a ℓ} (S : Semiring a ℓ) where

open Semiring S renaming (zero to *-zero)
open import Relation.Binary.Reasoning.Setoid setoid

import Algebra.Properties.Monoid.Mult.TCOptimised *-monoid as Mult
open import Algebra.Properties.Semiring.Exp S as U
  using () renaming (_^_ to _^ᵤ_)

------------------------------------------------------------------------
-- Re-export definition from the monoid

open import Algebra.Definitions.RawSemiring rawSemiring public
  using () renaming (_^′_ to _^_)

------------------------------------------------------------------------
-- Properties of _×_

^-congˡ : ∀ n → (_^ n) Preserves _≈_ ⟶ _≈_
^-congˡ = Mult.×-congʳ

^-cong : _^_ Preserves₂ _≈_ ⟶ _≡_ ⟶ _≈_
^-cong x≈y u≡v = Mult.×-cong u≡v x≈y

-- xᵐ⁺ⁿ ≈ xᵐxⁿ
^-homo-* : ∀ x m n → x ^ (m ℕ.+ n) ≈ (x ^ m) * (x ^ n)
^-homo-* = Mult.×-homo-+

-- (xᵐ)ⁿ≈xᵐ*ⁿ
^-assocʳ : ∀ x m n → (x ^ m) ^ n ≈ x ^ (m ℕ.* n)
^-assocʳ x m n rewrite ℕ.*-comm m n = Mult.×-assocˡ x n m
