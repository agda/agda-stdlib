------------------------------------------------------------------------
-- The Agda standard library
--
-- ℤ module n
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Mod where

open import Function using (_$_; _∘_)
open import Data.Bool using (true; false)
open import Data.Nat as ℕ using (ℕ; s≤s)
open import Data.Nat.Properties as ℕ
  using (m≤n⇒m≤1+n; 1+n≰n; module ≤-Reasoning)
open import Data.Fin as F hiding (suc; pred; _+_; _-_)
open import Data.Fin.Properties
open import Relation.Nullary using (Dec; yes; no; contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; module ≡-Reasoning)
import Algebra.Definitions as ADef

private variable
  m n : ℕ

open module AD {n} = ADef {A = Fin n} _≡_

private
  hs : ∀ {i : Fin (ℕ.suc n)} → i ≢ fromℕ n → Fin (ℕ.suc n)
  hs {i = i} i≢n = lower₁ (F.suc i) help
    where
    help : _
    help = i≢n ∘ sym ∘ toℕ-injective ∘ trans (toℕ-fromℕ _) ∘ cong ℕ.pred

suc : Fin n → Fin n
suc {ℕ.suc n} i with i ≟ fromℕ n
... | yes  _ = zero
... | no i≢n = hs i≢n

pred : Fin n → Fin n
pred zero = fromℕ _
pred (F.suc i) = inject₁ i

_ℕ+_ : ℕ → Fin n → Fin n
ℕ.zero ℕ+ i = i
ℕ.suc n ℕ+ i = suc (n ℕ+ i)

_+_ : Fin m → Fin n → Fin n
i + j = toℕ i ℕ+ j

_+‵_ : Fin n → Fin n → Fin n
_+‵_ = _+_

_-_ : Fin n → Fin n → Fin n
i - j  = i + opposite j

private
  inject₁≢fromℕ : {i : Fin n} → inject₁ i ≢ fromℕ n
  inject₁≢fromℕ {n} {i} i≡n = 1+n≰n $ begin-strict
    toℕ (fromℕ n)  ≡˘⟨ cong toℕ i≡n ⟩
    toℕ (inject₁ i) <⟨ inject₁ℕ< i ⟩
    n              ≡˘⟨ toℕ-fromℕ n ⟩
    toℕ (fromℕ n) ∎
    where open ≤-Reasoning

suc-inj≡fsuc : (i : Fin n) → suc (inject₁ i) ≡ F.suc i
suc-inj≡fsuc {n} i with inject₁ i ≟ fromℕ _
... | yes i≡n = contradiction i≡n inject₁≢fromℕ
... | no  i≢n = cong F.suc (toℕ-injective (trans (toℕ-lower₁ _ _) (toℕ-inject₁ _)))

pred-fsuc≡inj : (i : Fin n) → pred (F.suc i) ≡ inject₁ i
pred-fsuc≡inj _ = refl

suc-pred≡id : (i : Fin n) → suc (pred i) ≡ i
suc-pred≡id {ℕ.suc n} zero with fromℕ n ≟ fromℕ n
... | yes _  = refl
... | no n≢n = contradiction refl n≢n
suc-pred≡id {ℕ.suc n} (F.suc i) = suc-inj≡fsuc i

pred-suc≡id : (i : Fin n) → pred (suc i) ≡ i
pred-suc≡id {ℕ.suc n} i with i ≟ fromℕ n
... | yes refl = refl
... | no _ = inject₁-lower₁ _ _

+-identityˡ : LeftIdentity {ℕ.suc n} zero _+_
+-identityˡ _ = refl

+ℕ-identityʳ : ∀ {n′} (let n = ℕ.suc n′) → m ℕ.≤ n → toℕ (m ℕ+ zero {n}) ≡ m
+ℕ-identityʳ {ℕ.zero} m≤n = refl
+ℕ-identityʳ {ℕ.suc m} {n} (s≤s m≤n) with (m ℕ+ zero) ≟ F.suc (fromℕ n)
... | yes m+0≡sn = contradiction (begin-strict
  ℕ.suc n                ≡˘⟨ cong ℕ.suc (toℕ-fromℕ n) ⟩
  ℕ.suc (toℕ (fromℕ n)) ≡˘⟨ cong toℕ m+0≡sn ⟩
  toℕ (m ℕ+ zero)         ≡⟨ +ℕ-identityʳ (m≤n⇒m≤1+n m≤n) ⟩
  m                        <⟨ s≤s m≤n ⟩
  ℕ.suc n ∎) 1+n≰n
  where open ≤-Reasoning

... | no _ = cong ℕ.suc (begin
  toℕ (lower₁ (m ℕ+ zero) _) ≡⟨ toℕ-lower₁ (m ℕ+ zero) _ ⟩
  toℕ (m ℕ+ zero)            ≡⟨ +ℕ-identityʳ (m≤n⇒m≤1+n m≤n) ⟩
  m ∎)
  where open ≡-Reasoning

+-identityʳ : RightIdentity {ℕ.suc n} zero _+_
+-identityʳ {ℕ.zero} zero = refl
+-identityʳ {ℕ.suc _} = toℕ-injective ∘ +ℕ-identityʳ ∘ toℕ≤pred[n]
