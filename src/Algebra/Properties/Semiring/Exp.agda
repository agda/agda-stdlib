------------------------------------------------------------------------
-- The Agda standard library
--
-- Exponentiation defined over a semiring as repeated multiplication
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Data.Nat.Properties as ℕ

module Algebra.Properties.Semiring.Exp
  {a ℓ} (S : Semiring a ℓ) where

open Semiring S renaming (zero to *-zero)
open import Relation.Binary.Reasoning.Setoid setoid
import Algebra.Properties.Monoid.Mult *-monoid as Mult

------------------------------------------------------------------------
-- Definition

open import Algebra.Definitions.RawSemiring rawSemiring public
  using (_^_)

------------------------------------------------------------------------
-- Properties

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
