------------------------------------------------------------------------
-- The Agda standard library
--
-- ℤ module n
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Mod where

open import Function using (_$_; _∘_)
open import Data.Bool using (true; false)
open import Data.Product
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s)
open import Data.Nat.Properties as ℕ
  using (m≤n⇒m≤1+n; 1+n≰n; module ≤-Reasoning)
open import Data.Fin.Base as F hiding (suc; pred; _+_; _-_)
open import Data.Fin.Properties
open import Data.Fin.Relation.Unary.Top
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; module ≡-Reasoning)
import Algebra.Definitions as ADef

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

+ℕ-identityʳ-toℕ : ∀ {n′} (let n = ℕ.suc n′) (m≤n : m ℕ.≤ n′) →
  toℕ (m ℕ+ zero {n′}) ≡ m
+ℕ-identityʳ-toℕ {ℕ.zero} m≤n = refl
+ℕ-identityʳ-toℕ {ℕ.suc m} {n} (s≤s m≤n) = begin
  toℕ (suc (m ℕ+ zero)) ≡⟨ cong (toℕ ∘ suc) (toℕ-injective toℕm≡fromℕ<) ⟩
  toℕ (suc (inject₁ (fromℕ< (s≤s m≤n)))) ≡⟨ cong toℕ (suc-inj≡fsuc _) ⟩
  ℕ.suc (toℕ (fromℕ< (s≤s m≤n))) ≡⟨ cong ℕ.suc (toℕ-fromℕ< _) ⟩
  -- ? ≡⟨ ? ⟩
  ℕ.suc m ∎
  where

  toℕm≡fromℕ< = begin
    toℕ (m ℕ+ zero {n})        ≡⟨ +ℕ-identityʳ-toℕ (m≤n⇒m≤1+n m≤n) ⟩
    m                       ≡˘⟨ toℕ-fromℕ< _ ⟩
    toℕ (fromℕ< (s≤s m≤n)) ≡˘⟨ toℕ-inject₁ _ ⟩
    toℕ (inject₁ (fromℕ< (s≤s m≤n))) ∎


+ℕ-identityʳ : ∀ {n′} (let n = ℕ.suc n′) (m≤n : m ℕ.≤ n′) →
  m ℕ+ zero ≡ fromℕ< (s≤s m≤n)
+ℕ-identityʳ {ℕ.zero} z≤n = refl
+ℕ-identityʳ {ℕ.suc m} {n} (s≤s m≤n) = begin
  suc (m ℕ+ zero) ≡⟨ cong suc (+ℕ-identityʳ {m} (m≤n⇒m≤1+n m≤n)) ⟩
  suc (fromℕ< {m} {ℕ.suc n} (s≤s (m≤n⇒m≤1+n m≤n)))
    ≡⟨ cong suc (toℕ-injective helper2) ⟩
  suc (inject₁ (fromℕ< (s≤s m≤n))) ≡⟨ helper ⟩
  F.suc (fromℕ< (s≤s m≤n)) ∎

  where

  helper : suc (inject₁ (fromℕ< (s≤s m≤n))) ≡ F.suc (fromℕ< (s≤s m≤n))
  helper rewrite view-inject₁ $ fromℕ< $ s≤s m≤n = cong F.suc
    (view-complete (view $ fromℕ< (s≤s m≤n)))

  helper2 = trans (toℕ-fromℕ< _) (sym (trans (toℕ-inject₁ _) (toℕ-fromℕ< _)))

+-identityʳ : RightIdentity {ℕ.suc n} zero _+_
+-identityʳ {n} i rewrite +ℕ-identityʳ {m = toℕ i} {n} _ = fromℕ<-toℕ _ (toℕ≤pred[n] _)
