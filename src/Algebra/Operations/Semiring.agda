------------------------------------------------------------------------
-- The Agda standard library
--
-- Some defined operations (multiplication by natural number and
-- exponentiation)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Operations.Semiring {s₁ s₂} (S : Semiring s₁ s₂) where

import Algebra.Operations.CommutativeMonoid as MonoidOperations
open import Data.Nat.Base
  using (zero; suc; ℕ) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Product using (module Σ)
open import Function using (_$_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open Semiring S renaming (zero to *-zero)
open import Relation.Binary.Reasoning.Equational setoid

------------------------------------------------------------------------
-- Operations

-- Re-export all monoid operations and proofs
open MonoidOperations +-commutativeMonoid public

-- Exponentiation.
infixr 9 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero  = 1#
x ^ suc n = x * x ^ n

------------------------------------------------------------------------
-- Properties of _×_

-- _× 1# is homomorphic with respect to _ℕ*_/_*_.

×1-homo-* : ∀ m n → (m ℕ* n) × 1# ≈ (m × 1#) * (n × 1#)
×1-homo-* 0 n = begin
  0#             ≈⟨ sym (Σ.proj₁ *-zero (n × 1#)) ⟩
  0# * (n × 1#)  ∎
×1-homo-* (suc m) n = begin
  (n ℕ+ m ℕ* n) × 1#                  ≈⟨ ×-homo-+ 1# n (m ℕ* n) ⟩
  n × 1# + (m ℕ* n) × 1#              ≈⟨ +-cong refl (×1-homo-* m n) ⟩
  n × 1# + (m × 1#) * (n × 1#)         ≈⟨ sym (+-cong (*-identityˡ _) refl) ⟩
  1# * (n × 1#) + (m × 1#) * (n × 1#)  ≈⟨ sym (distribʳ (n × 1#) 1# (m × 1#)) ⟩
  (1# + m × 1#) * (n × 1#)             ∎

------------------------------------------------------------------------
-- Properties of _×′_

-- _×′ 1# is homomorphic with respect to _ℕ*_/_*_.

×′1-homo-* : ∀ m n → (m ℕ* n) ×′ 1# ≈ (m ×′ 1#) * (n ×′ 1#)
×′1-homo-* m n = begin
  (m ℕ* n) ×′ 1#         ≈⟨ sym $ ×≈×′ (m ℕ* n) 1# ⟩
  (m ℕ* n) ×  1#         ≈⟨ ×1-homo-* m n ⟩
  (m ×  1#) * (n ×  1#)  ≈⟨ *-cong (×≈×′ m 1#) (×≈×′ n 1#) ⟩
  (m ×′ 1#) * (n ×′ 1#)  ∎

------------------------------------------------------------------------
-- Properties of _^_

-- _^_ preserves equality.

^-congˡ : ∀ n → (_^ n) Preserves _≈_ ⟶ _≈_
^-congˡ zero    x≈y = refl
^-congˡ (suc n) x≈y = *-cong x≈y (^-congˡ n x≈y)

^-cong : _^_ Preserves₂ _≈_ ⟶ _≡_ ⟶ _≈_
^-cong {v = n} x≈y P.refl = ^-congˡ n x≈y
