------------------------------------------------------------------------
-- The Agda standard library
--
-- Combinatorics operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Combinatorics where

open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ; lower₁; _ℕ-ℕ_)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ; k+nℕ-ℕk≡n; toℕ-lower₁)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Combinatorics using (_!; n!≢0)
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Properties using (_≟_; 1+n≢0; m≢0∧n≢0⇒m*n≢0; *-identityʳ; *-identityˡ; suc-injective; *-distribˡ-+; *-distribʳ-+; *-assoc)
open import Data.Nat.Solver

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (fromWitnessFalse)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; module ≡-Reasoning; inspect; [_])
open import Function.Base using (_∘_)

open ≡-Reasoning

_C_ : (n : ℕ) → (k : Fin (suc n)) → ℕ
n C zero = 1
suc n C suc k with suc n ≟ toℕ (suc k)
... | yes 1+n≡1+k = 1
... | no  1+n≢1+k = (n C k) + (n C lower₁ (suc k) 1+n≢1+k)

nCn≡1 : (n : ℕ) → n C fromℕ n ≡ 1
nCn≡1 zero = refl
nCn≡1 (suc n) with suc n ≟ toℕ (fromℕ (suc n))
... | yes 1+n≡1+k = refl
... | no  1+n≢1+k = contradiction (cong suc (sym (toℕ-fromℕ n))) 1+n≢1+k

k!*[n-k]!*nCk≡n! : ∀ n k → toℕ k ! * (n ℕ-ℕ k) ! * n C k ≡ n !
k!*[n-k]!*nCk≡n!  zero    zero   = refl
k!*[n-k]!*nCk≡n! (suc n)  zero   = begin
  1 * (suc n !) * 1                    ≡⟨ *-identityʳ (1 * suc n !) ⟩
  1 * (suc n !)                        ≡⟨ *-identityˡ (suc n !) ⟩
  (suc n !)                            ∎
k!*[n-k]!*nCk≡n! (suc n) (suc k) with suc n ≟ toℕ (suc k)
... | yes 1+n≡1+k = begin
  (toℕ (suc k) !) * ((suc n ℕ-ℕ suc k) !) * 1 ≡˘⟨ cong (λ h → (h !) * (((suc n ℕ-ℕ suc k) !)) * 1) 1+n≡1+k ⟩
  suc n ! * ((suc n ℕ-ℕ suc k) !) * 1         ≡⟨ *-identityʳ _ ⟩
  suc n ! * ((suc n ℕ-ℕ suc k) !)             ≡⟨ cong (λ h → suc n ! * h !) (n-n≡0 (suc n) (suc k) 1+n≡1+k) ⟩
  suc n ! * 0 !                               ≡⟨⟩
  suc n ! * 1                                 ≡⟨ *-identityʳ _ ⟩
  suc n !                                     ∎
  where
    n-n≡0 : ∀ n k → (n ≡ toℕ k) → n ℕ-ℕ k ≡ 0
    n-n≡0  zero    zero   n≡k = refl
    n-n≡0 (suc n) (suc k) n≡k = n-n≡0 n k (suc-injective n≡k)
... | no  1+n≢1+k = begin
  (toℕ (suc k)) ! * ((suc n ℕ-ℕ suc k) !) * (n C k + n C k+1)                                         ≡⟨ *-distribˡ-+ ((toℕ (suc k)) ! * ((suc n ℕ-ℕ suc k) !)) (n C k) (n C k+1) ⟩
  (toℕ (suc k)) ! * ((suc n ℕ-ℕ suc k) !) * n C k + (toℕ (suc k)) ! * ((suc n ℕ-ℕ suc k) !) * n C k+1 ≡⟨ cong (λ h → h + ((toℕ (suc k)) ! * ((suc n ℕ-ℕ suc k) !) * n C k+1)) lemma₃ ⟩
  toℕ (suc k) * n ! + (toℕ (suc k)) ! * ((suc n ℕ-ℕ suc k) !) * n C k+1                               ≡⟨ cong (λ h → toℕ (suc k) * n ! + h) lemma₅ ⟩
  toℕ (suc k) * n ! + (suc n ℕ-ℕ suc k) * n !                                                         ≡˘⟨ *-distribʳ-+ (n !) (toℕ (suc k)) _ ⟩
  (toℕ (suc k) + (suc n ℕ-ℕ suc k)) * n !                                                             ≡⟨ cong (_* n !) (k+nℕ-ℕk≡n (suc n) (suc k)) ⟩
  (suc n) * n !                                                                                       ≡⟨⟩
  (suc n) !                                                                                           ∎
  where
    open +-*-Solver
    k+1 = lower₁ (suc k) 1+n≢1+k
    lemma₁ : ∀ a b c d → a * b * c * d ≡ a * (b * c * d)
    lemma₁ = solve 4 (λ a b c d → ((a :* b) :* c) :* d := a :* ((b :* c) :* d)) refl
    lemma₂ : ∀ a b c d → a * (b * c) * d ≡ b * (a * c * d)
    lemma₂ = solve 4 (λ a b c d → (a :* (b :* c)) :* d := b :* ((a :* c) :* d)) refl
    lemma₃ : toℕ (suc k) ! * (n ℕ-ℕ k) ! * n C k ≡ toℕ (suc k) * n !
    lemma₃ = begin
      toℕ (suc k) ! * (n ℕ-ℕ k) ! * n C k                                                             ≡⟨⟩
      ((toℕ (suc k) * toℕ k !) * (n ℕ-ℕ k) !) * n C k                                                 ≡⟨ lemma₁ (toℕ (suc k)) (toℕ k !) ((n ℕ-ℕ k) !) (n C k) ⟩
      toℕ (suc k) * (toℕ k ! * (n ℕ-ℕ k) ! * n C k)                                                   ≡⟨ cong (toℕ (suc k) *_) (k!*[n-k]!*nCk≡n! n k) ⟩
      toℕ (suc k) * n !                                                                               ∎
    lemma₄ : ∀ n k 1+n≢1+k → suc n ℕ-ℕ suc k ≡ suc (n ℕ-ℕ lower₁ (suc k) 1+n≢1+k)
    lemma₄  zero    zero   1+n≢1+k = contradiction refl 1+n≢1+k
    lemma₄ (suc n)  zero   1+n≢1+k = refl
    lemma₄ (suc n) (suc k) 1+n≢1+k = lemma₄ n k (1+n≢1+k ∘ cong suc)
    lemma₅ : toℕ (suc k) ! * (n ℕ-ℕ k) ! * n C k+1 ≡ (suc n ℕ-ℕ suc k) * n !
    lemma₅ = begin
      toℕ (suc k) ! *  (    n ℕ-ℕ     k) !                * n C k+1                                   ≡⟨⟩
      toℕ (suc k) ! *  (suc n ℕ-ℕ suc k) !                * n C k+1                                   ≡⟨ cong (λ h → toℕ (suc k) ! * h ! * n C k+1) (lemma₄ n k 1+n≢1+k) ⟩
      toℕ (suc k) ! *  suc (n ℕ-ℕ k+1)   !                * n C k+1                                   ≡⟨⟩
      toℕ (suc k) ! * (suc (n ℕ-ℕ k+1)   * (n ℕ-ℕ k+1) !) * n C k+1                                   ≡˘⟨ cong (λ h → h ! * (suc (n ℕ-ℕ k+1)   * (n ℕ-ℕ k+1) !) * n C k+1) (toℕ-lower₁ (suc k) 1+n≢1+k) ⟩
      toℕ    k+1  ! * (suc (n ℕ-ℕ k+1)   * (n ℕ-ℕ k+1) !) * n C k+1                                   ≡⟨ lemma₂ (toℕ k+1 !) (suc (n ℕ-ℕ k+1)) ((n ℕ-ℕ k+1) !) (n C k+1) ⟩
      suc (n ℕ-ℕ k+1)   * (toℕ k+1 !     * (n ℕ-ℕ k+1) !  * n C k+1)                                  ≡⟨ cong (suc (n ℕ-ℕ k+1) *_) (k!*[n-k]!*nCk≡n! n k+1) ⟩
      suc (n ℕ-ℕ k+1)   * n !                                                                         ≡˘⟨ cong (_* n !) (lemma₄ n k 1+n≢1+k) ⟩
      (suc n ℕ-ℕ suc k) * n !                                                                         ∎
