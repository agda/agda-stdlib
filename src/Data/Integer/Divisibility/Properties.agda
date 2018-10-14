------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility on ℤ
------------------------------------------------------------------------

module Data.Integer.Divisibility.Properties where

import Data.Nat as ℕ
import Data.Nat.Properties as NProp
import Data.Nat.Divisibility as Ndiv

import Data.Sign as S
import Data.Sign.Properties as SProp
open import Data.Integer
open import Data.Integer.Properties
open import Data.Integer.Divisibility as Zdiv
open import Data.Product
open import Function

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

signed-div : ∀ k i → k ∣ i → ∃ λ q → i ≡ q * k
signed-div k i (Ndiv.divides 0 eq) = + 0 , ∣n∣≡0⇒n≡0 eq
signed-div k i (Ndiv.divides q@(ℕ.suc q') eq) with k ≟ + 0
... | yes refl = + 0 , ∣n∣≡0⇒n≡0 (trans eq (NProp.*-zeroʳ q))
... | no ¬k≠0  = (S._*_ on sign) i k ◃ q , ◃-≡ sign-eq abs-eq  where

  k'   = ℕ.suc (ℕ.pred ∣ k ∣)
  ikq' = sign i S.* sign k ◃ ℕ.suc q'

  sign-eq : sign i ≡ sign (((S._*_ on sign) i k ◃ q) * k)
  sign-eq = sym $ begin
    sign (((S._*_ on sign) i k ◃ ℕ.suc q') * k)
      ≡⟨ cong (λ m → sign (sign ikq' S.* sign k ◃ ∣ ikq' ∣ ℕ.* m))
              (NProp.m≢0⇒m≡s[pred[m]] (¬k≠0 ∘ ∣n∣≡0⇒n≡0)) ⟩
    sign (sign ikq' S.* sign k ◃ ∣ ikq' ∣ ℕ.* k')
      ≡⟨ cong (λ m → sign (sign ikq' S.* sign k ◃ m ℕ.* k'))
              (abs-◃ (sign i S.* sign k) (ℕ.suc q')) ⟩
    sign (sign ikq' S.* sign k ◃ _)
      ≡⟨ sign-◃ (sign ikq' S.* sign k) (ℕ.pred ∣ k ∣ ℕ.+ q' ℕ.* k') ⟩
    sign ikq' S.* sign k
      ≡⟨ cong (S._* sign k) (sign-◃ (sign i S.* sign k) q') ⟩
    sign i S.* sign k S.* sign k
        ≡⟨ SProp.*-assoc (sign i) (sign k) (sign k) ⟩
    sign i S.* (sign k S.* sign k)
      ≡⟨ cong (sign i S.*_) (SProp.s*s≡+ (sign k)) ⟩
    sign i S.* S.+
      ≡⟨ SProp.*-identityʳ (sign i) ⟩
    sign i
      ∎ where open ≡-Reasoning

  abs-eq : ∣ i ∣ ≡ ∣ ((S._*_ on sign) i k ◃ q) * k ∣
  abs-eq = sym $ begin
    ∣ ((S._*_ on sign) i k ◃ ℕ.suc q') * k ∣
      ≡⟨ abs-◃ (sign ikq' S.* sign k) (∣ ikq' ∣ ℕ.* ∣ k ∣) ⟩
    ∣ ikq' ∣ ℕ.* ∣ k ∣
      ≡⟨ cong (ℕ._* ∣ k ∣) (abs-◃ (sign i S.* sign k) (ℕ.suc q')) ⟩
    ℕ.suc q' ℕ.* ∣ k ∣
      ≡⟨ sym eq ⟩
    ∣ i ∣
      ∎ where open ≡-Reasoning

*-monoʳ-∣ : ∀ k → (k *_) Preserves _∣_ ⟶ _∣_
*-monoʳ-∣ k {i} {j} i∣j = begin
  ∣ k * i ∣       ≡⟨ abs-*-commute k i ⟩
  ∣ k ∣ ℕ.* ∣ i ∣ ∣⟨ Ndiv.*-cong ∣ k ∣ i∣j ⟩
  ∣ k ∣ ℕ.* ∣ j ∣ ≡⟨ sym (abs-*-commute k j) ⟩
  ∣ k * j ∣ ∎ where open Ndiv.∣-Reasoning

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
  ℕ.suc (ℕ.pred ∣ k ∣) ℕ.* ∣ j ∣ ∎ where open Ndiv.∣-Reasoning

*-cancelʳ-∣ : ∀ k {i j} → k ≢ + 0 → i * k ∣ j * k → i ∣ j
*-cancelʳ-∣ k {i} {j}
  rewrite *-comm i k
        | *-comm j k
        = *-cancelˡ-∣ k
