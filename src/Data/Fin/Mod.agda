------------------------------------------------------------------------
-- The Agda standard library
--
-- ℤ module n
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Mod where

open import Function using (id; _$_; _∘_)
open import Data.Bool using (true; false)
open import Data.Product
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s)
open import Data.Nat.Properties as ℕ
  using (m≤n⇒m≤1+n; 1+n≰n; module ≤-Reasoning)
open import Data.Fin.Base as F hiding (suc; pred; _+_; _-_)
open import Data.Fin.Properties
open import Data.Fin.Induction using (<-weakInduction)
open import Data.Fin.Relation.Unary.Top
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; module ≡-Reasoning)
import Algebra.Definitions as ADef
open import Relation.Unary using (Pred)

private variable
  m n : ℕ

open module AD {n} = ADef {A = Fin n} _≡_
open ≡-Reasoning

infixl 6 _+_ _-_

suc : Fin n → Fin n
suc i with view i
... | ‵fromℕ = zero
... | ‵inj₁ i = F.suc ⟦ i ⟧

pred : Fin n → Fin n
pred zero = fromℕ _
pred (F.suc i) = inject₁ i

_ℕ+_ : ℕ → Fin n → Fin n
ℕ.zero ℕ+ i = i
ℕ.suc n ℕ+ i = suc (n ℕ+ i)

_+_ : Fin m → Fin n → Fin n
i + j = toℕ i ℕ+ j

_-_ : Fin n → Fin n → Fin n
i - j  = i + opposite j

suc-inj≡fsuc : (i : Fin n) → suc (inject₁ i) ≡ F.suc i
suc-inj≡fsuc i rewrite view-inject₁ i = cong F.suc (view-complete (view i))

sucFromℕ≡0 : ∀ n → suc (fromℕ n) ≡ zero
sucFromℕ≡0 n rewrite view-fromℕ n = refl

pred-fsuc≡inj : (i : Fin n) → pred (F.suc i) ≡ inject₁ i
pred-fsuc≡inj _ = refl

suc-pred≡id : (i : Fin n) → suc (pred i) ≡ i
suc-pred≡id zero = sucFromℕ≡0 _
suc-pred≡id (F.suc i) = suc-inj≡fsuc i

pred-suc≡id : (i : Fin n) → pred (suc i) ≡ i
pred-suc≡id i with view i
... | ‵fromℕ = refl
... | ‵inj₁ p = cong inject₁ (view-complete p)

+-identityˡ : LeftIdentity {ℕ.suc n} zero _+_
+-identityˡ _ = refl

+ℕ-identityʳ-toℕ : m ℕ.≤ n → toℕ (m ℕ+ zero {n}) ≡ m
+ℕ-identityʳ-toℕ {ℕ.zero} m≤n = refl
+ℕ-identityʳ-toℕ {ℕ.suc m} (s≤s m≤n) = begin
  toℕ (suc (m ℕ+ zero))                  ≡⟨ cong (toℕ ∘ suc) (toℕ-injective toℕm≡fromℕ<) ⟩
  toℕ (suc (inject₁ (fromℕ< (s≤s m≤n)))) ≡⟨ cong toℕ (suc-inj≡fsuc _) ⟩
  ℕ.suc (toℕ (fromℕ< (s≤s m≤n)))         ≡⟨ cong ℕ.suc (toℕ-fromℕ< _) ⟩
  ℕ.suc m ∎
  where

  toℕm≡fromℕ< = begin
    toℕ (m ℕ+ zero)        ≡⟨ +ℕ-identityʳ-toℕ (m≤n⇒m≤1+n m≤n) ⟩
    m                       ≡˘⟨ toℕ-fromℕ< _ ⟩
    toℕ (fromℕ< (s≤s m≤n)) ≡˘⟨ toℕ-inject₁ _ ⟩
    toℕ (inject₁ (fromℕ< (s≤s m≤n))) ∎

+ℕ-identityʳ : (m≤n : m ℕ.≤ n) → m ℕ+ zero ≡ fromℕ< (s≤s m≤n)
+ℕ-identityʳ {m} m≤n = toℕ-injective (begin
  toℕ (m ℕ+ zero) ≡⟨ +ℕ-identityʳ-toℕ m≤n ⟩
  m                 ≡˘⟨ toℕ-fromℕ< _ ⟩
  toℕ (fromℕ< (s≤s m≤n)) ∎)

+-identityʳ : RightIdentity {ℕ.suc n} zero _+_
+-identityʳ {n} i rewrite +ℕ-identityʳ {m = toℕ i} {n} _ = fromℕ<-toℕ _ (toℕ≤pred[n] _)

induction : ∀ {ℓ} (P : Pred (Fin (ℕ.suc n)) ℓ)
  → P zero
  → (∀ {i} → P i → P (suc i))
  → ∀ i → P i
induction P P₀ Pᵢ⇒Pᵢ₊₁ i = <-weakInduction P P₀ Pᵢ⇒Pᵢ₊₁′ i
  where

  PInj : ∀ {i} → P (suc (inject₁ i)) → P (F.suc i)
  PInj {i} rewrite suc-inj≡fsuc i = id

  Pᵢ⇒Pᵢ₊₁′ : ∀ i → P (inject₁ i) → P (F.suc i)
  Pᵢ⇒Pᵢ₊₁′ _ Pi = PInj (Pᵢ⇒Pᵢ₊₁ Pi)
