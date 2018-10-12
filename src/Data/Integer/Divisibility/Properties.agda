------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility on ℤ
------------------------------------------------------------------------

module Data.Integer.Divisibility.Properties where

import Data.Nat as ℕ
open import Data.Integer
open import Data.Integer.Properties
open import Data.Integer.Divisibility as Zdiv
import Data.Nat.Divisibility as Ndiv

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
