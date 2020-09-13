------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Rings
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- Disabled to prevent warnings from deprecated Table
{-# OPTIONS --warn=noUserWarning #-}

open import Algebra

module Algebra.Properties.CommutativeSemiring {r₁ r₂} (R : CommutativeSemiring r₁ r₂) where

open CommutativeSemiring R
open import Algebra.Properties.CommutativeMonoid +-commutativeMonoid
open import Algebra.Properties.SemiringWithoutOne semiringWithoutOne
open import Algebra.Operations.Semiring semiring

import Data.Nat.Base as ℕ
open import Data.Nat.Base using (ℕ; suc)
import Data.Nat.Properties as ℕ
open import Data.Nat.Properties using (≤-refl)
import Data.Fin.Base as Fin
open import Data.Fin.Base using (Fin; fromℕ; toℕ; punchIn; lower₁; inject₁; _ℕ-ℕ_)
open import Data.Fin.Properties using (_≟_; toℕ[k]≡n⇒k≡fromℕ[n]; k≡fromℕ[n]⇒toℕ[k]≡n; toℕ-inject₁-≢; lower₁-inject₁′; suc-injective; lower₁-irrelevant; toℕ-lower₁)
open import Data.Fin.Combinatorics using (_C_; nCn≡1)
open import Data.Table.Base using (lookup; tabulate)

open import Function using (_∘_)

open import Relation.Binary.Reasoning.Setoid setoid
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)

------------------------------------------------------------------------
-- Properties of _^_

binomial : ∀ n x y → ((x + y) ^ n) ≈ ∑[ i < suc n ] ((n C i) × (x ^ toℕ i) * (y ^ (n ℕ-ℕ i)))
binomial ℕ.zero   x y = begin
  ((x + y) ^ 0)                                             ≡⟨⟩
  1#                                                        ≈˘⟨ *-identityʳ 1# ⟩
  (1# * 1#)                                                 ≈˘⟨ *-congʳ (+-identityʳ 1#) ⟩
  (1 × 1# * 1#)                                             ≡⟨⟩
  (1 × (x ^ ℕ.zero) * (y ^ ℕ.zero))                         ≈˘⟨ +-identityʳ _ ⟩
  ((0 C Fin.zero) × (x ^ ℕ.zero) * (y ^ ℕ.zero)) + 0#       ≡⟨⟩
  (∑[ i < 1 ] ((0 C i) × (x ^ toℕ i) * (y ^ (0 ℕ-ℕ i))))    ∎
binomial (suc n) x y = begin
  ((x + y) ^ suc n)                                                       ≡⟨⟩
  (x + y) * (x + y) ^ n                                                   ≈⟨ *-congˡ (binomial n x y) ⟩
  (x + y) * ∑[ i < suc n ] bt n i                                         ≈⟨ distribʳ _ _ _ ⟩
  x * ∑[ i < suc n ] bt n i + y * ∑[ i < suc n ] bt n i                   ≈⟨ +-cong lemma₃ lemma₄ ⟩
  ∑[ i < suc (suc n) ] bt₁ n i + ∑[ i < suc (suc n) ] bt₂ n i             ≈˘⟨ ∑-distrib-+ _ (bt₁ n) (bt₂ n) ⟩
  ∑[ i < suc (suc n) ] (bt₁ n i + bt₂ n i)                                ≈⟨ sumₜ-cong-≈ lemma₈ ⟩
  ∑[ i < suc (suc n) ] bt (suc n) i ∎
  where
    bt : (n : ℕ) → (k : Fin (suc n)) → Carrier
    bt n k = ((n C k) × (x ^ toℕ k) * (y ^ (n ℕ-ℕ k)))
    bt₁ : (n : ℕ) → (k : Fin (suc (suc n))) → Carrier
    bt₁ n Fin.zero = 0#
    bt₁ n (Fin.suc k) = x * bt n k
    bt₂ : (n : ℕ) → (k : Fin (suc (suc n))) → Carrier
    bt₂ n k with k ≟ fromℕ (suc n)
    ... | yes k≡1+n = 0#
    ... | no  k≢1+n = y * bt n (lower₁ k (λ 1+n≡k → contradiction (toℕ[k]≡n⇒k≡fromℕ[n] (suc n) k (≡-sym 1+n≡k)) k≢1+n))
    bbt : (n : ℕ) → (k : Fin (suc n)) → Carrier
    bbt n k = (x ^ toℕ k) * (y ^ (n ℕ-ℕ k))
    lemma₁ : ∀ k → y * bt n k ≈ bt₂ n (inject₁ k)
    lemma₁ k with (inject₁ k) ≟ fromℕ (suc n)
    ... | yes k≡1+n = contradiction (k≡fromℕ[n]⇒toℕ[k]≡n (suc n) (inject₁ k) k≡1+n) (toℕ-inject₁-≢ k ∘ ≡-sym)
    ... | no  k≢1+n = sym (reflexive (cong (λ h → y * bt n h) (lower₁-inject₁′ k _)))
    lemma₂ : 0# ≈ bt₂ n (fromℕ (suc n))
    lemma₂ with fromℕ (suc n) ≟ fromℕ (suc n)
    ... | yes 1+n≡1+n = refl
    ... | no  1+n≢1+n = contradiction ≡-refl 1+n≢1+n
    lemma₃ : x * ∑[ i < suc n ] bt n i ≈ ∑[ i < suc (suc n) ] bt₁ n i
    lemma₃ = begin
      (x * ∑[ i < suc n ] bt n i)                                   ≈⟨ *-distribˡ-∑ (suc n) (bt n) x ⟩
      ∑[ i < suc n ] (x * bt n i)                                   ≈˘⟨ +-identityˡ _ ⟩
      (0# + ∑[ i < suc n ] (x * bt n i))                            ≡⟨⟩
      (0# + ∑[ i < suc n ] bt₁ n (punchIn Fin.zero i))              ≡⟨⟩
      (∑[ i < suc (suc n) ] bt₁ n i)                                ∎
    lemma₄ : y * ∑[ i < suc n ] bt n i ≈ ∑[ i < suc (suc n) ] bt₂ n i
    lemma₄ = begin
      (y * ∑[ i < suc n ] bt n i)                                                  ≈⟨ *-distribˡ-∑ (suc n) (bt n) y ⟩
      ∑[ i < suc n ] (y * bt n i)                                                  ≈˘⟨ +-identityʳ _ ⟩
      (∑[ i < suc n ] (y * bt n i) + 0#)                                           ≈⟨ +-cong (sumₜ-cong-≈ lemma₁) lemma₂ ⟩
      ((∑[ i < suc n ] bt₂ n (inject₁ i)) + bt₂ n (fromℕ (suc n)))                 ≈˘⟨ sumₜ-init (tabulate (bt₂ n)) ⟩
      sumₜ (tabulate (bt₂ n))                                                      ≡⟨⟩
      ∑[ i < suc (suc n) ] bt₂ n i                                                 ∎
    lemma₅ : ∀ k → x * bt n k ≈ (n C k) × bbt (suc n) (Fin.suc k)
    lemma₅ k = begin
      (x * bt n k)                                                                 ≡⟨⟩
      (x * ((n C k) × x ^ toℕ k * y ^ (n ℕ-ℕ k)))                                  ≈˘⟨ *-assoc x ((n C k) × x ^ toℕ k) (y ^ (n ℕ-ℕ k)) ⟩
      ((x * (n C k) × x ^ toℕ k) * y ^ (n ℕ-ℕ k))                                  ≈⟨ *-congʳ (×-comm (n C k) _ _) ⟩
      (((n C k) × x ^ toℕ (Fin.suc k)) * y ^ (suc n ℕ-ℕ Fin.suc k))                ≈⟨ ×-assoc (n C k) _ _ ⟩
      (n C k) × (x ^ toℕ (Fin.suc k) * y ^ (suc n ℕ-ℕ Fin.suc k))                  ≡⟨⟩
      (n C k) × bbt (suc n) (Fin.suc k)                                            ∎
    lemma₆ : ∀ k 1+n≢1+k → y * bt n (lower₁ (Fin.suc k) 1+n≢1+k) ≈ (n C lower₁ (Fin.suc k) 1+n≢1+k) × bbt (suc n) (Fin.suc k)
    lemma₆ k 1+n≢1+k = begin
      (y * bt n 1+k)                                                               ≡⟨⟩
      (y * ((n C 1+k) × x ^ toℕ 1+k * y ^ (n ℕ-ℕ 1+k)))                            ≈⟨ *-comm _ _ ⟩
      (((n C 1+k) × x ^ toℕ 1+k * y ^ (n ℕ-ℕ 1+k)) * y)                            ≈⟨ *-assoc _ _ _ ⟩
      ((n C 1+k) × x ^ toℕ 1+k * (y ^ (n ℕ-ℕ 1+k) * y))                            ≈⟨ *-congˡ (*-comm _ _) ⟩
      ((n C 1+k) × x ^ toℕ 1+k * y ^ suc (n ℕ-ℕ 1+k))                              ≡⟨ cong (λ h → (n C 1+k) × x ^ h * y ^ suc (n ℕ-ℕ 1+k)) (toℕ-lower₁ (Fin.suc k) 1+n≢1+k) ⟩
      ((n C 1+k) × x ^ toℕ (Fin.suc k) * y ^ suc (n ℕ-ℕ 1+k))                      ≡⟨ cong (λ h → (n C 1+k) × x ^ toℕ (Fin.suc k) * y ^ h) (1+[n-[1+k]]≡[1+n]-[1+k] n k 1+n≢1+k) ⟩
      ((n C 1+k) × x ^ toℕ (Fin.suc k) * y ^ (suc n ℕ-ℕ Fin.suc k))                ≈⟨ ×-assoc (n C 1+k) _ _ ⟩
      ((n C 1+k) × (x ^ toℕ (Fin.suc k) * y ^ (suc n ℕ-ℕ Fin.suc k)))              ≡⟨⟩
      ((n C 1+k) × bbt (suc n) (Fin.suc k))                                        ∎
      where
        1+k = lower₁ (Fin.suc k) 1+n≢1+k
        1+[n-[1+k]]≡[1+n]-[1+k] : ∀ n k 1+n≢1+k → suc (n ℕ-ℕ lower₁ (Fin.suc k) 1+n≢1+k) ≡ suc n ℕ-ℕ Fin.suc k
        1+[n-[1+k]]≡[1+n]-[1+k] ℕ.zero Fin.zero 1+n≢1+k = contradiction ≡-refl 1+n≢1+k
        1+[n-[1+k]]≡[1+n]-[1+k] (suc n) Fin.zero 1+n≢1+k = ≡-refl
        1+[n-[1+k]]≡[1+n]-[1+k] (suc n) (Fin.suc k) 1+n≢1+k = 1+[n-[1+k]]≡[1+n]-[1+k] n k (1+n≢1+k ∘ cong suc)
    lemma₇ : ∀ k 1+n≢1+k → n C k ℕ.+ n C (lower₁ (Fin.suc k) 1+n≢1+k) ≡ (suc n C Fin.suc k)
    lemma₇ k 1+n≢1+k with suc n ℕ.≟ toℕ (Fin.suc k)
    ... | yes 1+n≡1+k = contradiction 1+n≡1+k 1+n≢1+k
    ... | no  _       = cong (λ h → n C k ℕ.+ n C Fin.suc h) (lower₁-irrelevant k _ _)
    lemma₈ : ∀ k → bt₁ n k + bt₂ n k ≈ bt (suc n) k
    lemma₈ Fin.zero with Fin.zero ≟ fromℕ (suc n)
    ... | yes ()
    ... | no  0≢1+n = begin
      bt₁ n Fin.zero + bt₂ n Fin.zero     ≡⟨⟩
      0# + y * (1 × 1# * (y ^ n))         ≈⟨ +-identityˡ _ ⟩
      y * (1 × 1# * (y ^ n))              ≈˘⟨ *-assoc _ _ _ ⟩
      ((y * 1 × 1#) * y ^ n)              ≈⟨ *-congʳ (*-comm _ _) ⟩
      ((1 × 1# * y) * y ^ n)              ≈⟨ *-assoc _ _ _ ⟩
      (1 × 1# * (y * y ^ n))              ≡⟨⟩
      (1 × 1# * (y ^ suc n))              ≡⟨⟩
      bt (suc n) Fin.zero                 ∎
    lemma₈ (Fin.suc k) with Fin.suc k ≟ fromℕ (suc n)
    ... | yes 1+k≡1+n = begin
      (x * bt n k) + 0#                                                                       ≈⟨ +-identityʳ _ ⟩
      (x * bt n k)                                                                            ≡⟨ cong (λ h → x * bt n h) (suc-injective 1+k≡1+n) ⟩
      (x * bt n (fromℕ n))                                                                    ≡⟨⟩
      (x * ((n C fromℕ n) × (x ^ toℕ (fromℕ n)) * (y ^ (n ℕ-ℕ fromℕ n))))                     ≡⟨ cong (λ h → x * (h × (x ^ toℕ (fromℕ n)) * (y ^ (n ℕ-ℕ fromℕ n)))) (nCn≡1 n) ⟩
      (x * (1 × (x ^ toℕ (fromℕ n)) * (y ^ (n ℕ-ℕ fromℕ n))))                                 ≈⟨ *-congˡ (*-congʳ (+-identityʳ _)) ⟩
      (x * ((x ^ toℕ (fromℕ n)) * (y ^ (n ℕ-ℕ fromℕ n))))                                     ≈˘⟨ *-assoc x _ _ ⟩
      (x * (x ^ toℕ (fromℕ n))) * (y ^ (n ℕ-ℕ fromℕ n))                                       ≈˘⟨ *-congʳ (+-identityʳ _) ⟩
      (1 × (x * (x ^ (toℕ (fromℕ n)))) * (y ^ (n ℕ-ℕ fromℕ n)))                               ≡˘⟨ cong (λ h → h × (x ^ toℕ (fromℕ (suc n))) * (y ^ (n ℕ-ℕ fromℕ n))) (nCn≡1 (suc n)) ⟩
      ((suc n C fromℕ (suc n)) × (x ^ toℕ (fromℕ (suc n))) * (y ^ (suc n ℕ-ℕ fromℕ (suc n)))) ≡⟨⟩
      bt (suc n) (fromℕ (suc n))                                                              ≡˘⟨ cong (λ h → bt (suc n) h) 1+k≡1+n ⟩
      bt (suc n) (Fin.suc k)                                                                  ∎
    ... | no  1+k≢1+n = begin
      x * bt n k + y * bt n 1+k′                                                              ≈⟨ +-cong (lemma₅ k) (lemma₆ k laux) ⟩
      (n C k) × bbt (suc n) (Fin.suc k) + (n C 1+k′) × bbt (suc n) (Fin.suc k)                ≈˘⟨ ×-homo-+ (bbt (suc n) (Fin.suc k)) (n C k) (n C 1+k′) ⟩
      (n C k ℕ.+ n C 1+k′) × bbt (suc n) (Fin.suc k)                                          ≡⟨ cong (λ h → h × (bbt (suc n) (Fin.suc k))) (lemma₇ k laux) ⟩
      (suc n C Fin.suc k) × bbt (suc n) (Fin.suc k)                                           ≈˘⟨ ×-assoc (suc n C Fin.suc k) (x ^ toℕ (Fin.suc k)) (y ^ (suc n ℕ-ℕ Fin.suc k)) ⟩
      bt (suc n) (Fin.suc k)                                                                  ∎
      where
        laux : suc n ≢ toℕ (Fin.suc k)
        laux 1+n≡1+k = contradiction (toℕ[k]≡n⇒k≡fromℕ[n] (suc n) (Fin.suc k) (≡-sym 1+n≡1+k)) 1+k≢1+n
        1+k′ : Fin (suc n)
        1+k′ = lower₁ (Fin.suc k) laux
