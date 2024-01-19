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
open import Data.Fin.Properties as Fin hiding (suc-injective)
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
sucMod-inject₁ zero = refl
sucMod-inject₁ (suc i) rewrite sucMod-inject₁ i = refl

sucMod-fromℕ : ∀ n → sucMod (fromℕ n) ≡ zero
sucMod-fromℕ zero = refl
sucMod-fromℕ (suc n) rewrite sucMod-fromℕ n = refl

suc[fromℕ]≡zero : ∀ n → sucMod (fromℕ n) ≡ zero
suc[fromℕ]≡zero ℕ.zero                              = refl
suc[fromℕ]≡zero (ℕ.suc n) rewrite suc[fromℕ]≡zero n = refl

suc[fromℕ]≡zero⁻¹ : (i : Fin (ℕ.suc n)) → (sucMod i ≡ zero) → i ≡ fromℕ n
suc[fromℕ]≡zero⁻¹ {n = ℕ.zero}  zero        _ = refl
suc[fromℕ]≡zero⁻¹ {n = ℕ.suc _} (suc i) _ with zero ← sucMod i in eq
  = cong suc (suc[fromℕ]≡zero⁻¹ i eq)

suc[inject₁]≡suc[j] : (j : Fin n) → sucMod (inject₁ j) ≡ suc j
suc[inject₁]≡suc[j] zero                                      = refl
suc[inject₁]≡suc[j] (suc j) rewrite suc[inject₁]≡suc[j] j = refl

suc[inject₁]≡suc[j]⁻¹ : (i : Fin (ℕ.suc n)) {j : Fin n} →
                        (sucMod i ≡ suc j) → i ≡ inject₁ j
suc[inject₁]≡suc[j]⁻¹ zero        {zero} = λ _ → refl
suc[inject₁]≡suc[j]⁻¹ (suc i) {j}    with sucMod i in eqᵢ
... | zero      rewrite eqᵢ = λ ()
... | suc p rewrite eqᵢ = λ eq → begin
  suc i           ≡⟨ cong suc (suc[inject₁]≡suc[j]⁻¹ i eqᵢ) ⟩
  inject₁ (suc p) ≡⟨ cong inject₁ (Fin.suc-injective eq) ⟩
  inject₁ j ∎ where open ≡-Reasoning

suc-injective : {i j : Fin n} → sucMod i ≡ sucMod j → i ≡ j
suc-injective {n = n} {i} {j} eq with sucMod i in eqᵢ | sucMod j in eqⱼ
... | zero      | zero
    = trans (suc[fromℕ]≡zero⁻¹ i eqᵢ) (sym (suc[fromℕ]≡zero⁻¹ j eqⱼ))
... | suc p | suc q
    = begin
  i         ≡⟨ suc[inject₁]≡suc[j]⁻¹ i eqᵢ ⟩
  inject₁ p ≡⟨ cong inject₁ (Fin.suc-injective eq) ⟩
  inject₁ q ≡⟨ sym (suc[inject₁]≡suc[j]⁻¹ j eqⱼ) ⟩
  j ∎ where open ≡-Reasoning

------------------------------------------------------------------------
-- predMod

predMod-suc : (i : Fin n) → predMod (suc i) ≡ inject₁ i
predMod-suc _ = refl

predMod-sucMod : (i : Fin n) → predMod (sucMod i) ≡ i
predMod-sucMod {suc zero} zero = refl
predMod-sucMod {suc (suc n)} zero = refl
predMod-sucMod {suc (suc n)} (suc i) with sucMod i | predMod-sucMod i
... | zero   | eq rewrite eq = refl
... | suc c1 | eq rewrite eq = refl

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

+-identityˡ : .{{ _ : NonZero n }} → LeftIdentity zero⁺ _+_
+-identityˡ {suc n} i rewrite +ℕ-identityʳ {m = toℕ i} {n} _ = fromℕ<-toℕ _ (toℕ≤pred[n] _)

+-identityʳ : .{{ _ : NonZero n }} → RightIdentity zero⁺ _+_
+-identityʳ {suc _} _ = refl
