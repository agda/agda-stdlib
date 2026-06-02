------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of native binomial expansions over natural numbers.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Binomial.Properties where

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _^_)

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; cong₂; sym)

import Relation.Binary.PropositionalEquality as Eq

open Eq.≡-Reasoning

open import Data.Nat.Binomial.Base

------------------------------------------------------------------------
-- Distributivity and Absorption

-- Multiplying a single term by n increases its exponent by 1.
term-absorb : ∀ n k i → n * term n k i ≡ termSuc n k i
term-absorb n k i =
  begin
    n * ((k C i) * (n ^ i))
  ≡⟨ sym (*-assoc n (k C i) (n ^ i)) ⟩
    (n * (k C i)) * (n ^ i)
  ≡⟨ cong (λ x → x * (n ^ i)) (*-comm n (k C i)) ⟩
    ((k C i) * n) * (n ^ i)
  ≡⟨ *-assoc (k C i) n (n ^ i) ⟩
    (k C i) * (n * (n ^ i))
  ∎

-- Distributing n across the entire binomial summation.
*-distrib-sumBinomial : ∀ n k m → n * sumBinomial n k m ≡ sumBinomialSuc n k m
*-distrib-sumBinomial n k zero = term-absorb n k zero
*-distrib-sumBinomial n k (suc m) =
  begin
    n * (term n k (suc m) + sumBinomial n k m)
  ≡⟨ *-distribˡ-+ n (term n k (suc m)) (sumBinomial n k m) ⟩
    (n * term n k (suc m)) + (n * sumBinomial n k m)
  ≡⟨ cong₂ _+_ (term-absorb n k (suc m)) (*-distrib-sumBinomial n k m) ⟩
    termSuc n k (suc m) + sumBinomialSuc n k m
  ∎

------------------------------------------------------------------------
-- Pascal Index Alignment

-- Realigning terms using Pascal's identity to shift the binomial index.
pascal-term : ∀ n k m → termSuc n k m + term n k (suc m) ≡ term n (suc k) (suc m)
pascal-term n k m =
  begin
    ((k C m) * (n ^ suc m)) + ((k C suc m) * (n ^ suc m))
  ≡⟨ sym (*-distribʳ-+ (n ^ suc m) (k C m) (k C suc m)) ⟩
    ((k C m) + (k C suc m)) * (n ^ suc m)
  ≡⟨ refl ⟩
    (suc k C suc m) * (n ^ suc m)
  ∎

-- The zero-th term is invariant under increments of the upper index.
term-zero : ∀ n k → term n k 0 ≡ term n (suc k) 0
term-zero n k = refl

-- Rearrangement lemma for 4 summands.
+-rearrange₄ : ∀ a b c d → (a + b) + (c + d) ≡ a + (c + (b + d))
+-rearrange₄ a b c d =
  begin
    (a + b) + (c + d)
  ≡⟨ +-assoc a b (c + d) ⟩
    a + (b + (c + d))
  ≡⟨ cong (λ x → a + x) (sym (+-assoc b c d)) ⟩
    a + ((b + c) + d)
  ≡⟨ cong (λ x → a + (x + d)) (+-comm b c) ⟩
    a + ((c + b) + d)
  ≡⟨ cong (λ x → a + x) (+-assoc c b d) ⟩
    a + (c + (b + d))
  ∎

-- Aligning the sum of a standard expansion and its n-multiplied variant.
sumBinomial-align : ∀ n k m → sumBinomialSuc n k m + sumBinomial n k m ≡ termSuc n k m + sumBinomial n (suc k) m
sumBinomial-align n k zero = cong (λ x → termSuc n k 0 + x) (term-zero n k)
sumBinomial-align n k (suc m) =
  begin
    (termSuc n k (suc m) + sumBinomialSuc n k m) + (term n k (suc m) + sumBinomial n k m)
  ≡⟨ +-rearrange₄ (termSuc n k (suc m)) (sumBinomialSuc n k m) (term n k (suc m)) (sumBinomial n k m) ⟩
    termSuc n k (suc m) + (term n k (suc m) + (sumBinomialSuc n k m + sumBinomial n k m))
  ≡⟨ cong (λ x → termSuc n k (suc m) + (term n k (suc m) + x)) (sumBinomial-align n k m) ⟩
    termSuc n k (suc m) + (term n k (suc m) + (termSuc n k m + sumBinomial n (suc k) m))
  ≡⟨ cong (λ x → termSuc n k (suc m) + x) (sym (+-assoc (term n k (suc m)) (termSuc n k m) (sumBinomial n (suc k) m))) ⟩
    termSuc n k (suc m) + ((term n k (suc m) + termSuc n k m) + sumBinomial n (suc k) m)
  ≡⟨ cong (λ x → termSuc n k (suc m) + (x + sumBinomial n (suc k) m)) (+-comm (term n k (suc m)) (termSuc n k m)) ⟩
    termSuc n k (suc m) + ((termSuc n k m + term n k (suc m)) + sumBinomial n (suc k) m)
  ≡⟨ cong (λ x → termSuc n k (suc m) + (x + sumBinomial n (suc k) m)) (pascal-term n k m) ⟩
    termSuc n k (suc m) + (term n (suc k) (suc m) + sumBinomial n (suc k) m)
  ∎

------------------------------------------------------------------------
-- Boundary Collapse

-- Choosing a subset strictly larger than the set yields zero.
choose-greater : ∀ k d → k C (k + suc d) ≡ 0
choose-greater zero d = refl
choose-greater (suc k) d =
  begin
    (suc k) C (suc (k + suc d))
  ≡⟨ refl ⟩
    (k C (k + suc d)) + (k C (suc (k + suc d)))
  ≡⟨ cong (λ x → (k C (k + suc d)) + (k C x)) (sym (+-suc k (suc d))) ⟩
    (k C (k + suc d)) + (k C (k + suc (suc d)))
  ≡⟨ cong₂ _+_ (choose-greater k d) (choose-greater k (suc d)) ⟩
    0 + 0
  ≡⟨ refl ⟩
    0
  ∎

-- Choosing k + 1 from k yields zero.
choose-suc : ∀ k → k C suc k ≡ 0
choose-suc k =
  begin
    k C suc k
  ≡⟨ cong (λ x → k C x) (+-comm 1 k) ⟩
    k C (k + 1)
  ≡⟨ choose-greater k 0 ⟩
    0
  ∎

-- Choosing k from k yields one.
choose-diag : ∀ k → k C k ≡ 1
choose-diag zero = refl
choose-diag (suc k) =
  begin
    (suc k) C (suc k)
  ≡⟨ refl ⟩
    (k C k) + (k C suc k)
  ≡⟨ cong (λ x → (k C k) + x) (choose-suc k) ⟩
    (k C k) + 0
  ≡⟨ +-identityʳ (k C k) ⟩
    k C k
  ≡⟨ choose-diag k ⟩
    1
  ∎

-- The highest degree term simplifies using diagonal identities.
top-term : ∀ n k → termSuc n k k ≡ term n (suc k) (suc k)
top-term n k =
  begin
    (k C k) * (n ^ suc k)
  ≡⟨ cong (λ x → x * (n ^ suc k)) (choose-diag k) ⟩
    1 * (n ^ suc k)
  ≡⟨ sym (cong (λ x → x * (n ^ suc k)) (choose-diag (suc k))) ⟩
    (suc k C suc k) * (n ^ suc k)
  ∎

------------------------------------------------------------------------
-- Native Binomial Theorem

-- Standalone structural proof that (1 + n)^k = sum_{i=0}^k (k choose i) * n^i.
binomial-theorem : ∀ n k → (suc n) ^ k ≡ sumBinomial n k k
binomial-theorem n zero = refl
binomial-theorem n (suc k) =
  begin
    (suc n) ^ (suc k)
  ≡⟨ refl ⟩
    (suc n) * ((suc n) ^ k)
  ≡⟨ cong (λ x → (suc n) * x) (binomial-theorem n k) ⟩
    (suc n) * sumBinomial n k k
  ≡⟨ refl ⟩
    sumBinomial n k k + n * sumBinomial n k k
  ≡⟨ cong (λ x → sumBinomial n k k + x) (*-distrib-sumBinomial n k k) ⟩
    sumBinomial n k k + sumBinomialSuc n k k
  ≡⟨ +-comm (sumBinomial n k k) (sumBinomialSuc n k k) ⟩
    sumBinomialSuc n k k + sumBinomial n k k
  ≡⟨ sumBinomial-align n k k ⟩
    termSuc n k k + sumBinomial n (suc k) k
  ≡⟨ cong (λ x → x + sumBinomial n (suc k) k) (top-term n k) ⟩
    term n (suc k) (suc k) + sumBinomial n (suc k) k
  ≡⟨ refl ⟩
    sumBinomial n (suc k) (suc k)
  ∎
