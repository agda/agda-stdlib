------------------------------------------------------------------------
-- The Agda standard library
--
-- Exponentiation defined over a semiring as repeated multiplication
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Properties.Semiring.Exponentiation
  {a ℓ} (S : Semiring a ℓ) where

open import Data.Nat.Base using (zero; suc; ℕ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Semiring S renaming (zero to *-zero)
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Operations

-- Standard exponentiation.

infixr 9 _^_

_^_ : Carrier → ℕ → Carrier
x ^ zero  = 1#
x ^ suc n = x * x ^ n

------------------------------------------------------------------------
-- Properties of _^_

-- _^_ preserves equality.

^-congˡ : ∀ n → (_^ n) Preserves _≈_ ⟶ _≈_
^-congˡ zero    x≈y = refl
^-congˡ (suc n) x≈y = *-cong x≈y (^-congˡ n x≈y)

^-cong : _^_ Preserves₂ _≈_ ⟶ _≡_ ⟶ _≈_
^-cong {v = n} x≈y P.refl = ^-congˡ n x≈y
