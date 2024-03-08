------------------------------------------------------------------------
-- The Agda standard library
--
-- The Binomial Theorem for *-commuting elements in a Semiring
--
-- Freely adapted from PR #1287 by Maciej Piechotka (@uzytkownik)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Semiring)
open import Data.Bool.Base using (true)
open import Data.Nat.Base as ℕ hiding (_+_; _*_; _^_)
open import Data.Nat.Combinatorics
  using (_C_; nCn≡1; nC1≡n; nCk+nC[k+1]≡[n+1]C[k+1])
open import Data.Nat.Properties as ℕ
  using (<⇒<ᵇ; n<1+n; n∸n≡0; +-∸-assoc)
open import Data.Fin.Base as Fin
  using (Fin; zero; suc; toℕ; fromℕ; inject₁)
open import Data.Fin.Patterns using (0F)
open import Data.Fin.Properties as Fin
  using (toℕ<n; toℕ-fromℕ; toℕ-inject₁)
open import Data.Fin.Relation.Unary.Top
  using (view; ‵fromℕ; ‵inject₁; view-fromℕ; view-inject₁)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≢_; cong)

module Algebra.Properties.Semiring.Binomial
  {a ℓ} (S : Semiring a ℓ)
  (open Semiring S)
  (x y : Carrier)
  where

open import Algebra.Definitions _≈_
open import Algebra.Properties.Semiring.Sum S
open import Algebra.Properties.Semiring.Mult S
open import Algebra.Properties.Semiring.Exp S
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Definitions

-- Note - `n` could be implicit in many of these definitions, but the
-- code is more readable if left explicit.

binomial : (n : ℕ) → Fin (suc n) → Carrier
binomial n k = (x ^ toℕ k) * (y ^ (n ∸ toℕ k))

binomialTerm : (n : ℕ) → Fin (suc n) → Carrier
binomialTerm n k = (n C toℕ k) × binomial n k

binomialExpansion : ℕ → Carrier
binomialExpansion n = ∑[ k ≤ n ] (binomialTerm n k)

term₁ : (n : ℕ) → Fin (suc (suc n)) → Carrier
term₁ n zero    = 0#
term₁ n (suc k) = x * (binomialTerm n k)

term₂ : (n : ℕ) → Fin (suc (suc n)) → Carrier
term₂ n k with view k
... | ‵fromℕ     = 0#
... | ‵inject₁ j = y * binomialTerm n j

sum₁ : ℕ → Carrier
sum₁ n = ∑[ k ≤ suc n ] term₁ n k

sum₂ : ℕ → Carrier
sum₂ n = ∑[ k ≤ suc n ] term₂ n k

------------------------------------------------------------------------
-- Properties

term₂[n,n+1]≈0# : ∀ n → term₂ n (fromℕ (suc n)) ≈ 0#
term₂[n,n+1]≈0# n rewrite view-fromℕ (suc n) = refl

lemma₁ : ∀ n → x * binomialExpansion n ≈ sum₁ n
lemma₁ n = begin
  x * binomialExpansion n                ≈⟨ *-distribˡ-sum x (binomialTerm n) ⟩
  ∑[ i ≤ n ] (x * binomialTerm n i)      ≈⟨ +-identityˡ _ ⟨
  0# + ∑[ i ≤ n ] (x * binomialTerm n i) ≡⟨⟩
  0# + ∑[ i ≤ n ] term₁ n (suc i)        ≡⟨⟩
  sum₁ n                                 ∎

lemma₂ : ∀ n → y * binomialExpansion n ≈ sum₂ n
lemma₂ n = begin
  y * binomialExpansion n                       ≈⟨ *-distribˡ-sum y (binomialTerm n) ⟩
  ∑[ i ≤ n ] (y * binomialTerm n i)             ≈⟨ +-identityʳ _ ⟨
  ∑[ i ≤ n ] (y * binomialTerm n i) + 0#        ≈⟨ +-cong (sum-cong-≋ lemma₂-inject₁) (sym (term₂[n,n+1]≈0# n)) ⟩
  (∑[ i ≤ n ] term₂-inject₁ i) + term₂ n [n+1]  ≈⟨ sum-init-last (term₂ n) ⟨
  sum (term₂ n)                                 ≡⟨⟩
  sum₂ n                                        ∎
  where
    [n+1] = fromℕ (suc n)

    term₂-inject₁ : (i : Fin (suc n)) → Carrier
    term₂-inject₁ i = term₂ n (inject₁ i)

    lemma₂-inject₁ : ∀ i → y * binomialTerm n i ≈ term₂-inject₁ i
    lemma₂-inject₁ i rewrite view-inject₁ i = refl

------------------------------------------------------------------------
-- Next, a lemma which is independent of commutativity

x*lemma : ∀ {n} (i : Fin (suc n)) →
          x * binomialTerm n i ≈ (n C toℕ i) × binomial (suc n) (suc i)
x*lemma {n} i = begin
  x * binomialTerm n i                        ≡⟨⟩
  x * ((n C k) × (x ^ k * y ^ (n ∸ k)))       ≈⟨ *-congˡ (×-assoc-* (n C k) _ _) ⟨
  x * ((n C k) × x ^ k * y ^ (n ∸ k))         ≈⟨ *-assoc x ((n C k) × x ^ k) _ ⟨
  (x * (n C k) × x ^ k) * y ^ (n ∸ k)         ≈⟨ *-congʳ (×-comm-* (n C k) _ _) ⟩
  (n C k) × x ^ (suc k) * y ^ (n ∸ k)         ≡⟨⟩
  (n C k) × x ^ (suc k) * y ^ (suc n ∸ suc k) ≈⟨ ×-assoc-* (n C k) _ _ ⟩
  (n C k) × binomial (suc n) (suc i)          ∎
  where k = toℕ i

------------------------------------------------------------------------
-- Next, a lemma which does require commutativity

y*lemma : x * y ≈ y * x → ∀ {n : ℕ} (j : Fin n) →
          y * binomialTerm n (suc j) ≈ (n C toℕ (suc j)) × binomial (suc n) (suc (inject₁ j))
y*lemma x*y≈y*x {n} j = begin
  y * binomialTerm n (suc j)
    ≈⟨ ×-comm-* nC[j+1] y (binomial n (suc j)) ⟩
  nC[j+1] × (y * binomial n (suc j))
    ≈⟨ ×-congʳ nC[j+1] (y*x^m*y^n≈x^m*y^[n+1] x*y≈y*x [j+1] [n-j-1]) ⟩
  nC[j+1] × (x ^ [j+1] * y ^ [n-j])
    ≈⟨ ×-congʳ nC[j+1] (*-congʳ (^-congʳ x (cong suc k≡j))) ⟨
  nC[j+1] × (x ^ [k+1] * y ^ [n-j])
    ≈⟨ ×-congʳ nC[j+1] (*-congˡ (^-congʳ y [n-k]≡[n-j])) ⟨
  nC[j+1] × (x ^ [k+1] * y ^ [n-k])
    ≡⟨⟩
  nC[j+1] × (x ^ [k+1] * y ^ [n+1]-[k+1])
    ≡⟨⟩
  (n C toℕ (suc j)) × binomial (suc n) (suc i) ∎
  where
    i           = inject₁ j
    k           = toℕ i
    [k+1]       = ℕ.suc k
    [j+1]       = toℕ (suc j)
    [n-k]       = n ∸ k
    [n+1]-[k+1] = [n-k]
    [n-j-1]     = n ∸ [j+1]
    [n-j]       = ℕ.suc [n-j-1]
    nC[j+1]     = n C [j+1]

    k≡j : k ≡ toℕ j
    k≡j = toℕ-inject₁ j

    [n-k]≡[n-j] : [n-k] ≡ [n-j]
    [n-k]≡[n-j] = ≡.trans (cong (n ∸_) k≡j) (+-∸-assoc 1 (toℕ<n j))

------------------------------------------------------------------------
-- Now, a lemma characterising the sum of the term₁ and term₂ expressions

private
  n<ᵇ1+n : ∀ n → (n ℕ.<ᵇ suc n) ≡ true
  n<ᵇ1+n n with true ← n ℕ.<ᵇ suc n | _ ← <⇒<ᵇ (n<1+n n) = ≡.refl

term₁+term₂≈term : x * y ≈ y * x → ∀ n i → term₁ n i + term₂ n i ≈ binomialTerm (suc n) i

term₁+term₂≈term x*y≈y*x n 0F = begin
  term₁ n 0F + term₂ n 0F      ≡⟨⟩
  0# + y * (1 × (1# * y ^ n))  ≈⟨ +-identityˡ _ ⟩
  y * (1 × (1# * y ^ n))       ≈⟨ *-congˡ (+-identityʳ (1# * y ^ n)) ⟩
  y * (1# * y ^ n)             ≈⟨ *-congˡ (*-identityˡ (y ^ n)) ⟩
  y * y ^ n                    ≡⟨⟩
  y ^ suc n                    ≈⟨ *-identityˡ (y ^ suc n) ⟨
  1# * y ^ suc n               ≈⟨ +-identityʳ (1# * y ^ suc n) ⟨
  1 × (1# * y ^ suc n)         ≡⟨⟩
  binomialTerm (suc n) 0F      ∎

term₁+term₂≈term x*y≈y*x n (suc i) with view i
... | ‵fromℕ {n}
{- remembering that i = fromℕ n, definitionally -}
  rewrite toℕ-fromℕ n
    | nCn≡1 n
    | n∸n≡0 n
    | n<ᵇ1+n n
    = begin
  x * ((x ^ n * 1#) + 0#) + 0# ≈⟨ +-identityʳ _ ⟩
  x * ((x ^ n * 1#) + 0#)      ≈⟨ *-congˡ (+-identityʳ _) ⟩
  x * (x ^ n * 1#)             ≈⟨ *-assoc _ _ _ ⟨
  x * x ^ n * 1#               ≈⟨ +-identityʳ _ ⟨
  1 × (x * x ^ n * 1#)         ∎

... | ‵inject₁ j
{- remembering that i = inject₁ j, definitionally -}
    = begin
  (x * binomialTerm n i) + (y * binomialTerm n (suc j))
    ≈⟨ +-cong (x*lemma i) (y*lemma x*y≈y*x j) ⟩
  (nCk × [x^k+1]*[y^n-k]) + (nC[j+1] × [x^k+1]*[y^n-k])
    ≈⟨ +-congˡ (×-congˡ nC[k+1]≡nC[j+1]) ⟨
  (nCk × [x^k+1]*[y^n-k]) + (nC[k+1] × [x^k+1]*[y^n-k])
    ≈⟨ ×-homo-+ [x^k+1]*[y^n-k] nCk nC[k+1] ⟨
  (nCk ℕ.+ nC[k+1]) × [x^k+1]*[y^n-k]
    ≡⟨ cong (_× [x^k+1]*[y^n-k]) (nCk+nC[k+1]≡[n+1]C[k+1] n k) ⟩
  ((suc n) C (suc k)) × [x^k+1]*[y^n-k]
    ≡⟨⟩
  binomialTerm (suc n) (suc i) ∎
  where
    k               = toℕ i
    [k+1]           = ℕ.suc k
    [j+1]           = toℕ (suc j)
    nCk             = n C k
    nC[k+1]         = n C [k+1]
    nC[j+1]         = n C [j+1]
    [x^k+1]*[y^n-k] = binomial (suc n) (suc i)

    nC[k+1]≡nC[j+1] : nC[k+1] ≡ nC[j+1]
    nC[k+1]≡nC[j+1] = cong ((n C_) ∘ suc) (toℕ-inject₁ j)

------------------------------------------------------------------------
-- Finally, the main result

theorem : x * y ≈ y * x → ∀ n → (x + y) ^ n ≈ binomialExpansion n
theorem x*y≈y*x zero    = begin
  (x + y) ^ 0                     ≡⟨⟩
  1#                              ≈⟨ ×-homo-1 1# ⟨
  1 × 1#                          ≈⟨ *-identityʳ (1 × 1#) ⟨
  (1 × 1#) * 1#                   ≈⟨ ×-assoc-* 1 1# 1# ⟩
  1 × (1# * 1#)                   ≡⟨⟩
  1 × (x ^ 0 * y ^ 0)             ≈⟨ +-identityʳ _ ⟨
  1 × (x ^ 0 * y ^ 0) + 0#        ≡⟨⟩
  (0 C 0) × (x ^ 0 * y ^ 0) + 0#  ≡⟨⟩
  binomialExpansion 0             ∎
theorem x*y≈y*x n+1@(suc n) = begin
  (x + y) ^ n+1                                     ≡⟨⟩
  (x + y) * (x + y) ^ n                             ≈⟨ *-congˡ (theorem x*y≈y*x n) ⟩
  (x + y) * binomialExpansion n                     ≈⟨ distribʳ _ _ _ ⟩
  x * binomialExpansion n + y * binomialExpansion n ≈⟨ +-cong (lemma₁ n) (lemma₂ n) ⟩
  sum₁ n + sum₂ n                                   ≈⟨ ∑-distrib-+ (term₁ n) (term₂ n) ⟨
  ∑[ i ≤ n+1 ] (term₁ n i + term₂ n i)              ≈⟨ sum-cong-≋ (term₁+term₂≈term x*y≈y*x n) ⟩
  ∑[ i ≤ n+1 ] binomialTerm n+1 i                   ≡⟨⟩
  binomialExpansion n+1                             ∎
