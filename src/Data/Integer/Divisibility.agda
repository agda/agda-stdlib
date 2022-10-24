------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsigned divisibility
------------------------------------------------------------------------

-- For signed divisibility see `Data.Integer.Divisibility.Signed`

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Integer.Divisibility where

open import Function
open import Data.Integer.Base
open import Data.Integer.Properties
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕᵖ
import Data.Nat.Divisibility as ℕᵈ
import Data.Nat.Coprimality as ℕᶜ
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Divisibility

infix 4 _∣_

_∣_ : Rel ℤ 0ℓ
_∣_ = ℕᵈ._∣_ on ∣_∣

open ℕᵈ public using (divides)

------------------------------------------------------------------------
-- Properties of divisibility

*-monoʳ-∣ : ∀ k → (k *_) Preserves _∣_ ⟶ _∣_
*-monoʳ-∣ k {i} {j} i∣j = begin
  ∣ k * i ∣       ≡⟨ abs-* k i ⟩
  ∣ k ∣ ℕ.* ∣ i ∣ ∣⟨ ℕᵈ.*-monoʳ-∣ ∣ k ∣ i∣j ⟩
  ∣ k ∣ ℕ.* ∣ j ∣ ≡⟨ sym (abs-* k j) ⟩
  ∣ k * j ∣       ∎
  where open ℕᵈ.∣-Reasoning

*-monoˡ-∣ : ∀ k → (_* k) Preserves _∣_ ⟶ _∣_
*-monoˡ-∣ k {i} {j} rewrite *-comm i k | *-comm j k = *-monoʳ-∣ k

*-cancelˡ-∣ : ∀ k {i j} .{{_ : NonZero k}} → k * i ∣ k * j → i ∣ j
*-cancelˡ-∣ k {i} {j} k*i∣k*j = ℕᵈ.*-cancelˡ-∣ ∣ k ∣ $ begin
  ∣ k ∣ ℕ.* ∣ i ∣  ≡⟨ sym (abs-* k i) ⟩
  ∣ k * i ∣        ∣⟨ k*i∣k*j ⟩
  ∣ k * j ∣        ≡⟨ abs-* k j ⟩
  ∣ k ∣ ℕ.* ∣ j ∣  ∎
  where open ℕᵈ.∣-Reasoning

*-cancelʳ-∣ : ∀ k {i j} .{{_ : NonZero k}} → i * k ∣ j * k → i ∣ j
*-cancelʳ-∣ k {i} {j} rewrite *-comm i k | *-comm j k = *-cancelˡ-∣ k
