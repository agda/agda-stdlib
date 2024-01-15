------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to mod fin
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Mod.Properties where

open import Function.Base using (id; _$_; _∘_)
open import Data.Bool.Base using (true; false)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; s≤s; NonZero)
open import Data.Nat.Properties as ℕ
  using (m≤n⇒m≤1+n; 1+n≰n; module ≤-Reasoning)
open import Data.Fin.Base hiding (_+_; _-_)
open import Data.Fin.Properties
open import Data.Fin.Induction using (<-weakInduction)
open import Data.Fin.Relation.Unary.Top
open import Data.Fin.Mod
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)
open import Relation.Nullary.Negation.Core using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; module ≡-Reasoning)
open import Relation.Unary using (Pred)

module _ {n : ℕ} where
  open import Algebra.Definitions {A = Fin n} _≡_ public

open ≡-Reasoning

private variable
  m n : ℕ

------------------------------------------------------------------------
-- sucMod

sucMod-inject₁ : (i : Fin n) → sucMod (inject₁ i) ≡ suc i
sucMod-inject₁ i rewrite view-inject₁ i =
  cong suc (view-complete (view i))

sucMod-fromℕ : ∀ n → sucMod (fromℕ n) ≡ zero
sucMod-fromℕ n rewrite view-fromℕ n = refl

------------------------------------------------------------------------
-- predMod

predMod-suc : (i : Fin n) → predMod (suc i) ≡ inject₁ i
predMod-suc _ = refl

predMod-sucMod : (i : Fin n) → predMod (sucMod i) ≡ i
predMod-sucMod i with view i
... | ‵fromℕ = refl
... | ‵inj₁ p = cong inject₁ (view-complete p)

sucMod-predMod : (i : Fin n) → sucMod (predMod i) ≡ i
sucMod-predMod zero = sucMod-fromℕ _
sucMod-predMod (suc i) = sucMod-inject₁ i

------------------------------------------------------------------------
-- _+ℕ_

+ℕ-identityʳ-toℕ : m ℕ.≤ n → toℕ (m ℕ+ zero {n}) ≡ m
+ℕ-identityʳ-toℕ {zero} m≤n = refl
+ℕ-identityʳ-toℕ {suc m} 1+m≤1+n@(s≤s m≤n) = begin
  toℕ (sucMod (m ℕ+ zero))                ≡⟨ cong (toℕ ∘ sucMod) (toℕ-injective toℕm≡fromℕ<) ⟩
  toℕ (sucMod (inject₁ (fromℕ< 1+m≤1+n))) ≡⟨ cong toℕ (sucMod-inject₁ _) ⟩
  suc (toℕ (fromℕ< 1+m≤1+n))              ≡⟨ cong suc (toℕ-fromℕ< _) ⟩
  suc m                                     ∎
  where

  toℕm≡fromℕ< = begin
    toℕ (m ℕ+ zero)                ≡⟨ +ℕ-identityʳ-toℕ (m≤n⇒m≤1+n m≤n) ⟩
    m                                ≡⟨ toℕ-fromℕ< _ ⟨
    toℕ (fromℕ< 1+m≤1+n)           ≡⟨ toℕ-inject₁ _ ⟨
    toℕ (inject₁ (fromℕ< 1+m≤1+n)) ∎

+ℕ-identityʳ : (m≤n : m ℕ.≤ n) → m ℕ+ zero ≡ fromℕ< (s≤s m≤n)
+ℕ-identityʳ {m} m≤n = toℕ-injective (begin
  toℕ (m ℕ+ zero)        ≡⟨ +ℕ-identityʳ-toℕ m≤n ⟩
  m                        ≡⟨ toℕ-fromℕ< _ ⟨
  toℕ (fromℕ< (s≤s m≤n)) ∎)
  
------------------------------------------------------------------------
-- _+_

+-identityˡ : .{{ _ : NonZero n }} → LeftIdentity zeroFromNonZero _+_
+-identityˡ {suc _} _ = refl

+-identityʳ : .{{ _ : NonZero n }} → RightIdentity zeroFromNonZero _+_
+-identityʳ {suc n} i rewrite +ℕ-identityʳ {m = toℕ i} {n} _ = fromℕ<-toℕ _ (toℕ≤pred[n] _)

induction :
  ∀ {ℓ} (P : Pred (Fin (ℕ.suc n)) ℓ) →
  P zero →
  (∀ {i} → P i → P (sucMod i)) →
  ∀ i → P i
induction P P₀ Pᵢ⇒Pᵢ₊₁ i = <-weakInduction P P₀ Pᵢ⇒Pᵢ₊₁′ i
  where
  PInj : ∀ {i} → P (sucMod (inject₁ i)) → P (suc i)
  PInj {i} rewrite sucMod-inject₁ i = id

  Pᵢ⇒Pᵢ₊₁′ : ∀ i → P (inject₁ i) → P (suc i)
  Pᵢ⇒Pᵢ₊₁′ _ Pᵢ = PInj (Pᵢ⇒Pᵢ₊₁ Pᵢ)
