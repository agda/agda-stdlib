------------------------------------------------------------------------
-- The Agda standard library
--
-- Alternative definition of divisibility without using modulus.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Integer.Divisibility.Signed where

open import Function
open import Data.Integer
open import Data.Integer.Properties
open import Data.Integer.Divisibility as Unsigned
  using (divides)
  renaming (_∣_ to _∣ᵤ_)
import Data.Nat as ℕ
import Data.Nat.Divisibility as ℕ
import Data.Nat.Coprimality as ℕ
import Data.Nat.Properties as ℕ
import Data.Sign as S
import Data.Sign.Properties as SProp
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Relation.Binary.PreorderReasoning as PreorderReasoning
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as DEC

------------------------------------------------------------------------
-- Type

infix 4 _∣_

record _∣_ (k z : ℤ) : Set where
  constructor divides
  field quotient : ℤ
        equality : z ≡ quotient * k
open _∣_ using (quotient) public

------------------------------------------------------------------------
-- Conversion between signed and unsigned divisibility

∣ᵤ⇒∣ : ∀ {k i} → k ∣ᵤ i → k ∣ i
∣ᵤ⇒∣ {k} {i} (divides 0 eq) = divides (+ 0) (∣n∣≡0⇒n≡0 eq)
∣ᵤ⇒∣ {k} {i} (divides q@(ℕ.suc q') eq) with k ≟ + 0
... | yes refl = divides (+ 0) (∣n∣≡0⇒n≡0 (trans eq (ℕ.*-zeroʳ q)))
... | no ¬k≠0  = divides ((S._*_ on sign) i k ◃ q) (◃-≡ sign-eq abs-eq) where

  k'   = ℕ.suc (ℕ.pred ∣ k ∣)
  ikq' = sign i S.* sign k ◃ ℕ.suc q'

  sign-eq : sign i ≡ sign (((S._*_ on sign) i k ◃ q) * k)
  sign-eq = sym $ begin
    sign (((S._*_ on sign) i k ◃ ℕ.suc q') * k)
      ≡⟨ cong (λ m → sign (sign ikq' S.* sign k ◃ ∣ ikq' ∣ ℕ.* m))
              (sym (ℕ.m≢0⇒suc[pred[m]]≡m (¬k≠0 ∘ ∣n∣≡0⇒n≡0))) ⟩
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

∣⇒∣ᵤ : ∀ {k i} → k ∣ i → k ∣ᵤ i
∣⇒∣ᵤ {k} {i} (divides q eq) = divides ∣ q ∣ $′ begin
  ∣ i ∣           ≡⟨ cong ∣_∣ eq ⟩
  ∣ q * k ∣       ≡⟨ abs-*-commute q k ⟩
  ∣ q ∣ ℕ.* ∣ k ∣ ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- _∣_ is a preorder

∣-refl : Reflexive _∣_
∣-refl = ∣ᵤ⇒∣ ℕ.∣-refl

∣-reflexive : _≡_ ⇒ _∣_
∣-reflexive refl = ∣-refl

∣-trans : Transitive _∣_
∣-trans i∣j j∣k = ∣ᵤ⇒∣ (ℕ.∣-trans (∣⇒∣ᵤ i∣j) (∣⇒∣ᵤ j∣k))

∣-isPreorder : IsPreorder _≡_ _∣_
∣-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ∣-reflexive
  ; trans         = ∣-trans
  }

∣-preorder : Preorder _ _ _
∣-preorder = record { isPreorder = ∣-isPreorder }

module ∣-Reasoning = PreorderReasoning ∣-preorder
  hiding   (_≈⟨_⟩_)
  renaming (_∼⟨_⟩_ to _∣⟨_⟩_)

------------------------------------------------------------------------
-- Other properties of _∣_

_∣?_ : Decidable _∣_
k ∣? m = DEC.map′ ∣ᵤ⇒∣ ∣⇒∣ᵤ (∣ k ∣ ℕ.∣? ∣ m ∣)

0∣⇒≡0 : ∀ {m} → + 0 ∣ m → m ≡ + 0
0∣⇒≡0 0|m = ∣n∣≡0⇒n≡0 (ℕ.0∣⇒≡0 (∣⇒∣ᵤ 0|m))

m∣∣m∣ : ∀ {m} → m ∣ (+ ∣ m ∣)
m∣∣m∣ = ∣ᵤ⇒∣ ℕ.∣-refl

∣m∣∣m : ∀ {m} → (+ ∣ m ∣) ∣ m
∣m∣∣m = ∣ᵤ⇒∣ ℕ.∣-refl

∣m∣n⇒∣m+n : ∀ {i m n} → i ∣ m → i ∣ n → i ∣ m + n
∣m∣n⇒∣m+n (divides q refl) (divides p refl) =
  divides (q + p) (sym (*-distribʳ-+ _ q p))

∣m⇒∣-m : ∀ {i m} → i ∣ m → i ∣ - m
∣m⇒∣-m {i} {m} i∣m = ∣ᵤ⇒∣ $′ begin
  ∣ i ∣   ∣⟨ ∣⇒∣ᵤ i∣m ⟩
  ∣ m ∣   ≡⟨ sym (∣-n∣≡∣n∣ m) ⟩
  ∣ - m ∣ ∎
  where open ℕ.∣-Reasoning

∣m∣n⇒∣m-n : ∀ {i m n} → i ∣ m → i ∣ n → i ∣ m - n
∣m∣n⇒∣m-n i∣m i∣n = ∣m∣n⇒∣m+n i∣m (∣m⇒∣-m i∣n)

∣m+n∣m⇒∣n : ∀ {i m n} → i ∣ m + n → i ∣ m → i ∣ n
∣m+n∣m⇒∣n {i} {m} {n} i∣m+n i∣m = begin
  i             ∣⟨ ∣m∣n⇒∣m-n i∣m+n i∣m ⟩
  m + n - m     ≡⟨ +-comm (m + n) (- m) ⟩
  - m + (m + n) ≡⟨ sym (+-assoc (- m) m n) ⟩
  - m + m + n   ≡⟨ cong (_+ n) (+-inverseˡ m) ⟩
  + 0 + n       ≡⟨ +-identityˡ n ⟩
  n             ∎
  where open ∣-Reasoning

∣m+n∣n⇒∣m : ∀ {i m n} → i ∣ m + n → i ∣ n → i ∣ m
∣m+n∣n⇒∣m {i} {m} {n} i|m+n i|n
  rewrite +-comm m n
        = ∣m+n∣m⇒∣n i|m+n i|n

∣n⇒∣m*n : ∀ {i} m {n} → i ∣ n → i ∣ m * n
∣n⇒∣m*n {i} m {n} (divides q eq) = divides (m * q) $′ begin
  m * n       ≡⟨ cong (m *_) eq ⟩
  m * (q * i) ≡⟨ sym (*-assoc m q i) ⟩
  m * q * i   ∎
  where open ≡-Reasoning

∣m⇒∣m*n : ∀ {i m} n → i ∣ m → i ∣ m * n
∣m⇒∣m*n {i} {m} n i|m
  rewrite *-comm m n
        = ∣n⇒∣m*n {i} n {m} i|m

*-monoʳ-∣ : ∀ k → (k *_) Preserves _∣_ ⟶ _∣_
*-monoʳ-∣ k i∣j = ∣ᵤ⇒∣ (Unsigned.*-monoʳ-∣ k (∣⇒∣ᵤ i∣j))

*-monoˡ-∣ : ∀ k → (_* k) Preserves _∣_ ⟶ _∣_
*-monoˡ-∣ k {i} {j} i∣j = ∣ᵤ⇒∣ (Unsigned.*-monoˡ-∣ k {i} {j} (∣⇒∣ᵤ i∣j))

*-cancelˡ-∣ : ∀ k {i j} → k ≢ + 0 → k * i ∣ k * j → i ∣ j
*-cancelˡ-∣ k k≢0 = ∣ᵤ⇒∣ ∘ Unsigned.*-cancelˡ-∣ k k≢0 ∘ ∣⇒∣ᵤ

*-cancelʳ-∣ : ∀ k {i j} → k ≢ + 0 → i * k ∣ j * k → i ∣ j
*-cancelʳ-∣ k {i} {j} k≢0 = ∣ᵤ⇒∣ ∘′ Unsigned.*-cancelʳ-∣ k {i} {j} k≢0 ∘′ ∣⇒∣ᵤ
