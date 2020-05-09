------------------------------------------------------------------------
-- The Agda standard library
--
-- Unsigned divisibility
------------------------------------------------------------------------

-- For signed divisibility see `Data.Integer.Divisibility.Signed`

{-# OPTIONS --without-K --safe #-}

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
  ∣ k * i ∣       ≡⟨ abs-*-commute k i ⟩
  ∣ k ∣ ℕ.* ∣ i ∣ ∣⟨ ℕᵈ.*-monoʳ-∣ ∣ k ∣ i∣j ⟩
  ∣ k ∣ ℕ.* ∣ j ∣ ≡⟨ sym (abs-*-commute k j) ⟩
  ∣ k * j ∣       ∎
  where open ℕᵈ.∣-Reasoning

*-monoˡ-∣ : ∀ k → (_* k) Preserves _∣_ ⟶ _∣_
*-monoˡ-∣ k {i} {j}
  rewrite *-comm i k
        | *-comm j k
        = *-monoʳ-∣ k

*-cancelˡ-∣ : ∀ k {i j} → k ≢ + 0 → k * i ∣ k * j → i ∣ j
*-cancelˡ-∣ k {i} {j} k≢0 k*i∣k*j = ℕᵈ.*-cancelˡ-∣ (ℕ.pred ∣ k ∣) $ begin
  let ∣k∣-is-suc = ℕᵖ.suc[pred[n]]≡n (k≢0 ∘ ∣n∣≡0⇒n≡0) in
  ℕ.suc (ℕ.pred ∣ k ∣) ℕ.* ∣ i ∣ ≡⟨ cong (ℕ._* ∣ i ∣) (∣k∣-is-suc) ⟩
  ∣ k ∣ ℕ.* ∣ i ∣                ≡⟨ sym (abs-*-commute k i) ⟩
  ∣ k * i ∣                      ∣⟨ k*i∣k*j ⟩
  ∣ k * j ∣                      ≡⟨ abs-*-commute k j ⟩
  ∣ k ∣ ℕ.* ∣ j ∣                ≡⟨ cong (ℕ._* ∣ j ∣) (sym ∣k∣-is-suc) ⟩
  ℕ.suc (ℕ.pred ∣ k ∣) ℕ.* ∣ j ∣ ∎
  where open ℕᵈ.∣-Reasoning

*-cancelʳ-∣ : ∀ k {i j} → k ≢ + 0 → i * k ∣ j * k → i ∣ j
*-cancelʳ-∣ k {i} {j} ≢0 = *-cancelˡ-∣ k ≢0 ∘
  subst₂ _∣_ (*-comm i k) (*-comm j k)
