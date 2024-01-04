------------------------------------------------------------------------
-- The Agda standard library
--
-- ℕ module n
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Mod where

open import Function.Base using (id; _$_; _∘_)
open import Data.Bool.Base using (true; false)
open import Data.Product.Base
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s; NonZero)
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

open module AD {n} = ADef {A = Fin n} _≡_
open ≡-Reasoning

private variable
  m n : ℕ

infixl 6 _+_ _-_

sucAbsorb : Fin n → Fin n
sucAbsorb i with view i
... | ‵fromℕ = zero
... | ‵inj₁ i = F.suc ⟦ i ⟧

predAbsorb : Fin n → Fin n
predAbsorb zero = fromℕ _
predAbsorb (F.suc i) = inject₁ i

_ℕ+_ : ℕ → Fin n → Fin n
ℕ.zero ℕ+ i = i
ℕ.suc n ℕ+ i = sucAbsorb (n ℕ+ i)

_+_ : Fin m → Fin n → Fin n
i + j = toℕ i ℕ+ j

_-_ : Fin m → Fin n → Fin m
i - j  = opposite j + i

suc-inject₁ : (i : Fin n) → sucAbsorb (inject₁ i) ≡ F.suc i
suc-inject₁ i rewrite view-inject₁ i = cong F.suc (view-complete (view i))

suc-fromℕ : ∀ n → sucAbsorb (fromℕ n) ≡ zero
suc-fromℕ n rewrite view-fromℕ n = refl

pred-sucAbsorb : (i : Fin n) → predAbsorb (F.suc i) ≡ inject₁ i
pred-sucAbsorb _ = refl

suc-pred≡id : (i : Fin n) → sucAbsorb (predAbsorb i) ≡ i
suc-pred≡id zero = suc-fromℕ _
suc-pred≡id (F.suc i) = suc-inject₁ i

pred-suc : (i : Fin n) → predAbsorb (sucAbsorb i) ≡ i
pred-suc i with view i
... | ‵fromℕ = refl
... | ‵inj₁ p = cong inject₁ (view-complete p)

+-identityˡ : LeftIdentity {ℕ.suc n} zero _+_
+-identityˡ _ = refl

+ℕ-identityʳ-toℕ : m ℕ.≤ n → toℕ (m ℕ+ zero {n}) ≡ m
+ℕ-identityʳ-toℕ {ℕ.zero} m≤n = refl
+ℕ-identityʳ-toℕ {ℕ.suc m} (s≤s m≤n) = begin
  toℕ (sucAbsorb (m ℕ+ zero))                  ≡⟨ cong (toℕ ∘ sucAbsorb) (toℕ-injective toℕm≡fromℕ<) ⟩
  toℕ (sucAbsorb (inject₁ (fromℕ< (s≤s m≤n)))) ≡⟨ cong toℕ (suc-inject₁ _) ⟩
  ℕ.suc (toℕ (fromℕ< (s≤s m≤n)))         ≡⟨ cong ℕ.suc (toℕ-fromℕ< _) ⟩
  ℕ.suc m ∎
  where

  toℕm≡fromℕ< = begin
    toℕ (m ℕ+ zero)        ≡⟨ +ℕ-identityʳ-toℕ (m≤n⇒m≤1+n m≤n) ⟩
    m                      ≡˘⟨ toℕ-fromℕ< _ ⟩
    toℕ (fromℕ< (s≤s m≤n)) ≡˘⟨ toℕ-inject₁ _ ⟩
    toℕ (inject₁ (fromℕ< (s≤s m≤n))) ∎

+ℕ-identityʳ : (m≤n : m ℕ.≤ n) → m ℕ+ zero ≡ fromℕ< (s≤s m≤n)
+ℕ-identityʳ {m} m≤n = toℕ-injective (begin
  toℕ (m ℕ+ zero) ≡⟨ +ℕ-identityʳ-toℕ m≤n ⟩
  m                 ≡˘⟨ toℕ-fromℕ< _ ⟩
  toℕ (fromℕ< (s≤s m≤n)) ∎)

+-identityʳ : .⦃ n≢0 : NonZero n ⦄ → RightIdentity {n = n} zeroFromNonZero _+_
+-identityʳ {ℕ.suc n} i rewrite +ℕ-identityʳ {m = toℕ i} {n} _ = fromℕ<-toℕ _ (toℕ≤pred[n] _)

induction : ∀ {ℓ} (P : Pred (Fin (ℕ.suc n)) ℓ)
  → P zero
  → (∀ {i} → P i → P (sucAbsorb i))
  → ∀ i → P i
induction P P₀ Pᵢ⇒Pᵢ₊₁ i = <-weakInduction P P₀ Pᵢ⇒Pᵢ₊₁′ i
  where

  PInj : ∀ {i} → P (sucAbsorb (inject₁ i)) → P (F.suc i)
  PInj {i} rewrite suc-inject₁ i = id

  Pᵢ⇒Pᵢ₊₁′ : ∀ i → P (inject₁ i) → P (F.suc i)
  Pᵢ⇒Pᵢ₊₁′ _ Pi = PInj (Pᵢ⇒Pᵢ₊₁ Pi)
