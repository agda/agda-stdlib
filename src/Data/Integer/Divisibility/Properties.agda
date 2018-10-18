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
import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- _∣_ and _∣′_ are equivalent

∣m⇒∣′m : ∀ {k i} → k ∣ i → k ∣′ i
∣m⇒∣′m {k} {i} (Ndiv.divides 0 eq) = divides (+ 0) (∣n∣≡0⇒n≡0 eq)
∣m⇒∣′m {k} {i} (Ndiv.divides q@(ℕ.suc q') eq) with k ≟ + 0
... | yes refl = divides (+ 0) (∣n∣≡0⇒n≡0 (trans eq (NProp.*-zeroʳ q)))
... | no ¬k≠0  = divides ((S._*_ on sign) i k ◃ q) (◃-≡ sign-eq abs-eq) where

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

∣′m⇒∣m : ∀ {k i} → k ∣′ i → k ∣ i
∣′m⇒∣m {k} {i} (divides q eq) = Ndiv.divides ∣ q ∣ $′ begin
  ∣ i ∣           ≡⟨ cong ∣_∣ eq ⟩
  ∣ q * k ∣       ≡⟨ abs-*-commute q k ⟩
  ∣ q ∣ ℕ.* ∣ k ∣ ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- _∣′_ is a preorder

∣′-refl : Reflexive _∣′_
∣′-refl = ∣m⇒∣′m Ndiv.∣-refl

∣′-reflexive : _≡_ ⇒ _∣′_
∣′-reflexive refl = ∣′-refl

∣′-trans : Transitive _∣′_
∣′-trans i∣j j∣k = ∣m⇒∣′m (Ndiv.∣-trans (∣′m⇒∣m i∣j) (∣′m⇒∣m j∣k))

∣′-isPreorder : IsPreorder _≡_ _∣′_
∣′-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ∣′-reflexive
  ; trans         = ∣′-trans
  }

∣′-preorder : Preorder _ _ _
∣′-preorder = record { isPreorder = ∣′-isPreorder }

module ∣′-Reasoning = PreorderReasoning ∣′-preorder
  hiding   (_≈⟨_⟩_)
  renaming (_∼⟨_⟩_ to _∣′⟨_⟩_)

------------------------------------------------------------------------
-- Properties of _∣′_

0∣′⇒≡0 : ∀ {m} → + 0 ∣′ m → m ≡ + 0
0∣′⇒≡0 0|m = ∣n∣≡0⇒n≡0 (Ndiv.0∣⇒≡0 (∣′m⇒∣m 0|m))

m∣′∣m∣ : ∀ {m} → m ∣′ + ∣ m ∣
m∣′∣m∣ = ∣m⇒∣′m Ndiv.∣-refl

∣m∣∣′m : ∀ {m} → + ∣ m ∣ ∣′ m
∣m∣∣′m = ∣m⇒∣′m Ndiv.∣-refl

∣′m∣′n⇒∣′m+n : ∀ {i m n} → i ∣′ m → i ∣′ n → i ∣′ m + n
∣′m∣′n⇒∣′m+n {i} {m} {n} (divides q eqq) (divides p eqp) = divides (q + p) $′ begin
  m + n         ≡⟨ cong₂ _+_ eqq eqp ⟩
  q * i + p * i ≡⟨ sym (*-distribʳ-+ i q p) ⟩
  (q + p) * i   ∎ where open ≡-Reasoning

∣′m⇒∣′-m : ∀ {i m} → i ∣′ m → i ∣′ - m
∣′m⇒∣′-m {i} {m} i∣m = ∣m⇒∣′m $′ begin
  ∣ i ∣   ∣⟨ ∣′m⇒∣m i∣m ⟩
  ∣ m ∣   ≡⟨ sym (∣-n∣≡∣n∣ m) ⟩
  ∣ - m ∣ ∎ where open Ndiv.∣-Reasoning

∣′m∣′n⇒∣′m-n : ∀ {i m n} → i ∣′ m → i ∣′ n → i ∣′ m - n
∣′m∣′n⇒∣′m-n i∣m i∣n = ∣′m∣′n⇒∣′m+n i∣m (∣′m⇒∣′-m i∣n)

∣′m+n∣′m⇒∣′n : ∀ {i m n} → i ∣′ m + n → i ∣′ m → i ∣′ n
∣′m+n∣′m⇒∣′n {i} {m} {n} i∣m+n i∣m = begin
  i             ∣′⟨ ∣′m∣′n⇒∣′m-n i∣m+n i∣m ⟩
  m + n - m     ≡⟨ +-comm (m + n) (- m) ⟩
  - m + (m + n) ≡⟨ sym (+-assoc (- m) m n) ⟩
  - m + m + n   ≡⟨ cong (_+ n) (+-inverseˡ m) ⟩
  + 0 + n       ≡⟨ +-identityˡ n ⟩
  n ∎ where open ∣′-Reasoning

∣′m+n∣′n⇒∣′m : ∀ {i m n} → i ∣′ m + n → i ∣′ n → i ∣′ m
∣′m+n∣′n⇒∣′m {i} {m} {n} i|m+n i|n
  rewrite +-comm m n
        = ∣′m+n∣′m⇒∣′n i|m+n i|n

∣′n⇒∣′m*n : ∀ {i} m {n} → i ∣′ n → i ∣′ m * n
∣′n⇒∣′m*n {i} m {n} (divides q eq) = divides (m * q) $′ begin
  m * n       ≡⟨ cong (m *_) eq ⟩
  m * (q * i) ≡⟨ sym (*-assoc m q i) ⟩
  m * q * i   ∎ where open ≡-Reasoning

∣′m⇒∣′m*n : ∀ {i m} n → i ∣′ m → i ∣′ m * n
∣′m⇒∣′m*n {i} {m} n i|m
  rewrite *-comm m n
        = ∣′n⇒∣′m*n {i} n {m} i|m

*-monoʳ-∣ : ∀ k → (k *_) Preserves _∣_ ⟶ _∣_
*-monoʳ-∣ k {i} {j} i∣j = begin
  ∣ k * i ∣       ≡⟨ abs-*-commute k i ⟩
  ∣ k ∣ ℕ.* ∣ i ∣ ∣⟨ Ndiv.*-cong ∣ k ∣ i∣j ⟩
  ∣ k ∣ ℕ.* ∣ j ∣ ≡⟨ sym (abs-*-commute k j) ⟩
  ∣ k * j ∣ ∎ where open Ndiv.∣-Reasoning

*-monoʳ-∣′ : ∀ k → (k *_) Preserves _∣′_ ⟶ _∣′_
*-monoʳ-∣′ k i∣j = ∣m⇒∣′m (*-monoʳ-∣ k (∣′m⇒∣m i∣j))

*-monoˡ-∣ : ∀ k → (_* k) Preserves _∣_ ⟶ _∣_
*-monoˡ-∣ k {i} {j}
  rewrite *-comm i k
        | *-comm j k
        = *-monoʳ-∣ k

*-monoˡ-∣′ : ∀ k → (_* k) Preserves _∣′_ ⟶ _∣′_
*-monoˡ-∣′ k {i} {j} i∣j = ∣m⇒∣′m (*-monoˡ-∣ k {i} {j} (∣′m⇒∣m i∣j))

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
