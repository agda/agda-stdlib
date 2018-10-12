------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility on ℤ
------------------------------------------------------------------------

module Data.Integer.Divisibility.Properties where

import Data.Nat as ℕ
import Data.Nat.Properties as NProp
import Data.Nat.Divisibility as Ndiv

open import Data.Integer
open import Data.Integer.Properties
open import Data.Integer.Divisibility as Zdiv
open import Function

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open Ndiv.∣-Reasoning

*-monoʳ-∣ : ∀ k → (k *_) Preserves _∣_ ⟶ _∣_
*-monoʳ-∣ k {i} {j} i∣j = begin
  ∣ k * i ∣       ≡⟨ abs-*-commute k i ⟩
  ∣ k ∣ ℕ.* ∣ i ∣ ∣⟨ Ndiv.*-cong ∣ k ∣ i∣j ⟩
  ∣ k ∣ ℕ.* ∣ j ∣ ≡⟨ sym (abs-*-commute k j) ⟩
  ∣ k * j ∣ ∎

*-monoˡ-∣ : ∀ k → (_* k) Preserves _∣_ ⟶ _∣_
*-monoˡ-∣ k {i} {j}
  rewrite *-comm i k
        | *-comm j k
        = *-monoʳ-∣ k

*-cancelˡ-∣ : ∀ k {i j} → k ≢ + 0 → k * i ∣ k * j → i ∣ j
*-cancelˡ-∣ k {i} {j} k≢0 k*i∣k*j = Ndiv./-cong (ℕ.pred ∣ k ∣) $ begin
  let ∣k∣-is-suc = NProp.m≢0⇒m≡s[pred[m]] (k≢0 ∘ ∣n∣≡0⇒n≡0) in
  ℕ.suc (ℕ.pred ∣ k ∣) ℕ.* ∣ i ∣ ≡⟨ cong (ℕ._* ∣ i ∣) (sym ∣k∣-is-suc) ⟩
  ∣ k ∣ ℕ.* ∣ i ∣                ≡⟨ sym (abs-*-commute k i) ⟩
  ∣ k * i ∣                      ∣⟨ k*i∣k*j ⟩
  ∣ k * j ∣                      ≡⟨ abs-*-commute k j ⟩
  ∣ k ∣ ℕ.* ∣ j ∣                ≡⟨ cong (ℕ._* ∣ j ∣) ∣k∣-is-suc ⟩
  ℕ.suc (ℕ.pred ∣ k ∣) ℕ.* ∣ j ∣ ∎

*-cancelʳ-∣ : ∀ k {i j} → k ≢ + 0 → i * k ∣ j * k → i ∣ j
*-cancelʳ-∣ k {i} {j}
  rewrite *-comm i k
        | *-comm j k
        = *-cancelˡ-∣ k
