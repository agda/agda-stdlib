------------------------------------------------------------------------
-- The Agda standard library
--
-- Alternative definition of divisibility without using modulus.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Integer.Divisibility.Signed where

open import Function.Base using (_⟨_⟩_; _$_; _$′_; _∘_; _∘′_)
open import Data.Integer.Base
open import Data.Integer.Properties
import Data.Integer.Divisibility as Unsigned
import Data.Nat.Base as ℕ
import Data.Nat.Divisibility as ℕ
import Data.Nat.Coprimality as ℕ
import Data.Nat.Properties as ℕ
import Data.Sign as Sign
import Data.Sign.Properties as Sign
open import Level
open import Relation.Binary.Core using (_⇒_; _Preserves_⟶_)
open import Relation.Binary.Bundles using (Preorder)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; Decidable)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Preorder as ≲-Reasoning
open import Relation.Nullary.Decidable as Dec using (yes; no)
open import Relation.Binary.Reasoning.Syntax

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

∣ᵤ⇒∣ : ∀ {k i} → k Unsigned.∣ i → k ∣ i
∣ᵤ⇒∣ {k} {i} (Unsigned.divides 0           eq) = divides (+ 0) (∣i∣≡0⇒i≡0 eq)
∣ᵤ⇒∣ {k} {i} (Unsigned.divides q@(ℕ.suc _) eq) with k ≟ +0
... | yes refl = divides +0 (∣i∣≡0⇒i≡0 (trans eq (ℕ.*-zeroʳ q)))
... | no  neq  = divides (sign i Sign.* sign k ◃ q) (◃-cong sign-eq abs-eq)
  where
  ikq = sign i Sign.* sign k ◃ q

  *-nonZero : ∀ m n .{{_ : ℕ.NonZero m}} .{{_ : ℕ.NonZero n}} → ℕ.NonZero (m ℕ.* n)
  *-nonZero (ℕ.suc _) (ℕ.suc _) = _

  ◃-nonZero : ∀ s n .{{_ : ℕ.NonZero n}} → NonZero (s ◃ n)
  ◃-nonZero Sign.- (ℕ.suc _) = _
  ◃-nonZero Sign.+ (ℕ.suc _) = _

  ikq≢0 : NonZero ikq
  ikq≢0 = ◃-nonZero (sign i Sign.* sign k) q

  instance
    ikq*∣k∣≢0 : ℕ.NonZero (∣ ikq ∣ ℕ.* ∣ k ∣)
    ikq*∣k∣≢0 = *-nonZero ∣ ikq ∣ ∣ k ∣ {{ikq≢0}} {{≢-nonZero neq}}

  sign-eq : sign i ≡ sign (ikq * k)
  sign-eq = sym $ begin
    sign (ikq * k)                        ≡⟨ sign-◃ (sign ikq Sign.* sign k) (∣ ikq ∣ ℕ.* ∣ k ∣) ⟩
    sign ikq Sign.* sign k                ≡⟨ cong (Sign._* sign k) (sign-◃ (sign i Sign.* sign k) q) ⟩
    (sign i Sign.* sign k) Sign.* sign k  ≡⟨ Sign.*-assoc (sign i) (sign k) (sign k) ⟩
    sign i Sign.* (sign k Sign.* sign k)  ≡⟨ cong (sign i Sign.*_) (Sign.s*s≡+ (sign k)) ⟩
    sign i Sign.* Sign.+                  ≡⟨ Sign.*-identityʳ (sign i) ⟩
    sign i                          ∎
    where open ≡-Reasoning

  abs-eq : ∣ i ∣ ≡ ∣ ikq * k ∣
  abs-eq = sym $ begin
    ∣ ikq * k ∣        ≡⟨ ∣i*j∣≡∣i∣*∣j∣ ikq k ⟩
    ∣ ikq ∣ ℕ.* ∣ k ∣  ≡⟨ cong (ℕ._* ∣ k ∣) (abs-◃ (sign i Sign.* sign k) q) ⟩
    q ℕ.* ∣ k ∣        ≡⟨ sym eq ⟩
    ∣ i ∣              ∎
    where open ≡-Reasoning

∣⇒∣ᵤ : ∀ {k i} → k ∣ i → k Unsigned.∣ i
∣⇒∣ᵤ {k} {i} (divides q eq) = Unsigned.divides ∣ q ∣ $′ begin
  ∣ i ∣           ≡⟨ cong ∣_∣ eq ⟩
  ∣ q * k ∣       ≡⟨ abs-* q k ⟩
  ∣ q ∣ ℕ.* ∣ k ∣ ∎
  where open ≡-Reasoning

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

------------------------------------------------------------------------
-- Divisibility reasoning

module ∣-Reasoning where
  private module Base = ≲-Reasoning ∣-preorder

  open Base public
    hiding (step-≲; step-∼; step-≈; step-≈˘)
    renaming (≲-go to ∣-go)

  open ∣-syntax _IsRelatedTo_ _IsRelatedTo_ ∣-go public

------------------------------------------------------------------------
-- Other properties of _∣_

infix 4 _∣?_

_∣?_ : Decidable _∣_
k ∣? m = Dec.map′ ∣ᵤ⇒∣ ∣⇒∣ᵤ (∣ k ∣ ℕ.∣? ∣ m ∣)

0∣⇒≡0 : ∀ {m} → 0ℤ ∣ m → m ≡ 0ℤ
0∣⇒≡0 0|m = ∣i∣≡0⇒i≡0 (ℕ.0∣⇒≡0 (∣⇒∣ᵤ 0|m))

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
  ∣ m ∣   ≡⟨ sym (∣-i∣≡∣i∣ m) ⟩
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
∣m+n∣n⇒∣m {m = m} {n} i|m+n i|n rewrite +-comm m n = ∣m+n∣m⇒∣n i|m+n i|n

∣n⇒∣m*n : ∀ {i} m {n} → i ∣ n → i ∣ m * n
∣n⇒∣m*n {i} m {n} (divides q eq) = divides (m * q) $′ begin
  m * n       ≡⟨ cong (m *_) eq ⟩
  m * (q * i) ≡⟨ sym (*-assoc m q i) ⟩
  m * q * i   ∎
  where open ≡-Reasoning

∣m⇒∣m*n : ∀ {i m} n → i ∣ m → i ∣ m * n
∣m⇒∣m*n {m = m} n i|m rewrite *-comm m n = ∣n⇒∣m*n n i|m

*-monoʳ-∣ : ∀ k → (k *_) Preserves _∣_ ⟶ _∣_
*-monoʳ-∣ k = ∣ᵤ⇒∣ ∘ Unsigned.*-monoʳ-∣ k ∘ ∣⇒∣ᵤ

*-monoˡ-∣ : ∀ k → (_* k) Preserves _∣_ ⟶ _∣_
*-monoˡ-∣ k {i} {j} = ∣ᵤ⇒∣ ∘ Unsigned.*-monoˡ-∣ k {i} {j} ∘ ∣⇒∣ᵤ

*-cancelˡ-∣ : ∀ k {i j} .{{_ : NonZero k}} → k * i ∣ k * j → i ∣ j
*-cancelˡ-∣ k = ∣ᵤ⇒∣ ∘ Unsigned.*-cancelˡ-∣ k ∘ ∣⇒∣ᵤ

*-cancelʳ-∣ : ∀ k {i j} .{{_ : NonZero k}} → i * k ∣ j * k → i ∣ j
*-cancelʳ-∣ k {i} {j} = ∣ᵤ⇒∣ ∘′ Unsigned.*-cancelʳ-∣ k {i} {j} ∘′ ∣⇒∣ᵤ
