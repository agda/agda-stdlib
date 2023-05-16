------------------------------------------------------------------------
-- The Agda standard library
--
-- Combinatorial operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Nat.Combinatorics where

open import Data.Nat.Base
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

import Data.Nat.Combinatorics.Base          as Base
import Data.Nat.Combinatorics.Specification as Specification
import Algebra.Properties.CommutativeSemigroup as CommSemigroupProperties

open ≤-Reasoning

private
  variable
    n k : ℕ

------------------------------------------------------------------------
-- Definitions

open Base public
  using (_P_; _C_)

------------------------------------------------------------------------
-- Properties of _P_

open Specification public
  using (nPk≡n!/[n∸k]!; k>n⇒nPk≡0; [n∸k]!k!∣n!)

nPn≡n! : ∀ n → n P n ≡ n !
nPn≡n! n = begin-equality
  n P n           ≡⟨ nPk≡n!/[n∸k]! (≤-refl {n}) ⟩
  n ! / (n ∸ n) ! ≡⟨ /-congʳ (cong _! (n∸n≡0 n)) ⟩
  n ! / 0 !       ≡⟨⟩
  n ! / 1         ≡⟨ n/1≡n (n !) ⟩
  n !             ∎
  where instance
    _ = (n ∸ n) !≢0

nP1≡n : ∀ n → n P 1 ≡ n
nP1≡n zero        = refl
nP1≡n n@(suc n-1) = begin-equality
  n P 1          ≡⟨ nPk≡n!/[n∸k]! (s≤s (z≤n {n-1})) ⟩
  n ! / n-1 !    ≡⟨ m*n/n≡m n (n-1 !) ⟩
  n              ∎
  where instance
    _ = n-1 !≢0

------------------------------------------------------------------------
-- Properties of _C_

open Specification public
  using (nCk≡n!/k![n-k]!; k>n⇒nCk≡0)

nCk≡nC[n∸k] : k ≤ n → n C k ≡ n C (n ∸ k)
nCk≡nC[n∸k] {k} {n} k≤n = begin-equality
  n C k                               ≡⟨ nCk≡n!/k![n-k]! k≤n ⟩
  n ! / (k ! * (n ∸ k) !)             ≡˘⟨ /-congʳ (*-comm ((n ∸ k) !) (k !)) ⟩
  n ! / ((n ∸ k) ! * k !)             ≡˘⟨ /-congʳ (cong ((n ∸ k) ! *_) (cong _! (m∸[m∸n]≡n k≤n))) ⟩
  n ! / ((n ∸ k) ! * (n ∸ (n ∸ k)) !) ≡˘⟨ nCk≡n!/k![n-k]! (m≤n⇒n∸m≤n k≤n) ⟩
  n C (n ∸ k)                         ∎
  where instance
    _ = (n ∸ k) !* k !≢0
    _ = k !* (n ∸ k) !≢0
    _ = (n ∸ k) !* (n ∸ (n ∸ k)) !≢0

nCk≡nPk/k! : k ≤ n → n C k ≡ (n P k / k !) {{k !≢0}}
nCk≡nPk/k! {k} {n} k≤n = begin-equality
  n C k                   ≡⟨ nCk≡n!/k![n-k]! k≤n ⟩
  n ! / (k ! * (n ∸ k) !) ≡˘⟨ /-congʳ (*-comm ((n ∸ k)!) (k !)) ⟩
  n ! / ((n ∸ k) ! * k !) ≡˘⟨ m/n/o≡m/[n*o] (n !) ((n ∸ k) !) (k !) ⟩
  (n ! / (n ∸ k) !) / k ! ≡˘⟨ /-congˡ (nPk≡n!/[n∸k]! k≤n) ⟩
  (n P k) / k !           ∎
  where instance
    _ = k !≢0
    _ = (n ∸ k) !≢0
    _ = (n ∸ k) !* k !≢0
    _ = k !* (n ∸ k) !≢0

nCn≡1 : ∀ n → n C n ≡ 1
nCn≡1 n = begin-equality
  n C n          ≡⟨ nCk≡nPk/k! (≤-refl {n}) ⟩
  (n P n) / n !  ≡⟨ /-congˡ (nPn≡n! n) ⟩
  n ! / n !      ≡⟨ n/n≡1 (n !) ⟩
  1              ∎
  where instance
    _ = n !≢0

nC1≡n : ∀ n → n C 1 ≡ n
nC1≡n zero    = refl
nC1≡n n@(suc n-1) = begin-equality
  n C 1          ≡⟨ nCk≡nPk/k!  (s≤s (z≤n {n-1})) ⟩
  (n P 1) / 1 !  ≡⟨ n/1≡n (n P 1) ⟩
  n P 1          ≡⟨ nP1≡n n ⟩
  n              ∎


------------------------------------------------------------------------
-- Arithmetic of (n C k)

module _ {n k} (k<n : k < n) where

  private

    [n-k]            = n ∸ k
    [n-k-1]          = n ∸ suc k

    [n-k]!           = [n-k] !
    [n-k-1]!         = [n-k-1] !

    [n-k]≡1+[n-k-1]  : [n-k] ≡ suc [n-k-1]
    [n-k]≡1+[n-k-1]  = +-∸-assoc 1 k<n


  [n-k]*[n-k-1]!≡[n-k]! : [n-k] * [n-k-1]! ≡ [n-k]!
  [n-k]*[n-k-1]!≡[n-k]! = begin-equality
      [n-k] * [n-k-1]!
        ≡⟨ cong (_* [n-k-1]!) [n-k]≡1+[n-k-1] ⟩
      (suc [n-k-1]) * [n-k-1]!
        ≡˘⟨ cong _! [n-k]≡1+[n-k-1] ⟩
      [n-k]!                ∎

  private

    n!           = n !
    k!           = k !
    [k+1]!       = (suc k) !

    d[k]         = k! * [n-k]!
    [k+1]*d[k]   = (suc k) * d[k]
    d[k+1]       = [k+1]! * [n-k-1]!
    [n-k]*d[k+1] = [n-k] * d[k+1]

  [n-k]*d[k+1]≡[k+1]*d[k] : [n-k]*d[k+1] ≡ [k+1]*d[k]
  [n-k]*d[k+1]≡[k+1]*d[k] = begin-equality
    [n-k]*d[k+1]
      ≡⟨ x∙yz≈y∙xz [n-k] [k+1]! [n-k-1]! ⟩
    [k+1]! * ([n-k] * [n-k-1]!)
      ≡⟨ *-assoc (suc k) k! ([n-k] * [n-k-1]!) ⟩
    (suc k) * (k! * ([n-k] * [n-k-1]!))
       ≡⟨ cong ((suc k) *_) (cong (k! *_) [n-k]*[n-k-1]!≡[n-k]!) ⟩
    [k+1]*d[k]             ∎
    where open CommSemigroupProperties *-commutativeSemigroup

k![n∸k]!∣n! : ∀ {n k} → k ≤ n → k ! * (n ∸ k) ! ∣ n !
k![n∸k]!∣n! {n} {k} k≤n = subst (_∣ n !) (*-comm ((n ∸ k) !) (k !)) ([n∸k]!k!∣n! k≤n)

nCk+nC[k+1]≡[n+1]C[k+1] : ∀ n k → n C k + n C (suc k) ≡ suc n C suc k
nCk+nC[k+1]≡[n+1]C[k+1] n k with <-cmp k n
{- case k>n, in which case 1+k>1+n>n -}
... | tri> _ _ k>n = begin-equality
  n C k + n C (suc k) ≡⟨ cong (_+ (n C (suc k))) (k>n⇒nCk≡0 k>n) ⟩
  0 + n C (suc k)     ≡⟨⟩
  n C (suc k)         ≡⟨ k>n⇒nCk≡0 (m<n⇒m<1+n k>n) ⟩
  0                   ≡˘⟨ k>n⇒nCk≡0 (s<s k>n) ⟩
  suc n C suc k       ∎
{- case k≡n, in which case 1+k≡1+n>n -}
... | tri≈ _ k≡n _ rewrite k≡n = begin-equality
  n C n + n C (suc n) ≡⟨ cong (n C n +_) (k>n⇒nCk≡0 (n<1+n n)) ⟩
  n C n + 0           ≡⟨ +-identityʳ (n C n) ⟩
  n C n               ≡⟨ nCn≡1 n ⟩
  1                   ≡˘⟨ nCn≡1 (suc n) ⟩
  suc n C suc n       ∎
{- case k<n, in which case 1+k<1+n and there's arithmetic to perform -}
... | tri< k<n _ _ = begin-equality
  n C k + n C (suc k)
    ≡⟨ cong (n C k +_) (nCk≡n!/k![n-k]! k<n)  ⟩
  n C k + (n! / d[k+1])
    ≡˘⟨ cong (n C k +_) (m*n/m*o≡n/o (n ∸ k) n! d[k+1]) ⟩
  n C k + [n-k]*n!/[n-k]*d[k+1]
    ≡⟨ cong (_+ [n-k]*n!/[n-k]*d[k+1]) (nCk≡n!/k![n-k]! k≤n) ⟩
  n! / d[k] + _
    ≡˘⟨ cong (_+ [n-k]*n!/[n-k]*d[k+1]) (m*n/m*o≡n/o (suc k) n! d[k]) ⟩
  (suc k * n!) / [k+1]*d[k] + _
    ≡⟨ cong (((suc k * n!) / [k+1]*d[k]) +_) (/-congʳ ([n-k]*d[k+1]≡[k+1]*d[k] k<n)) ⟩
  (suc k * n!) / [k+1]*d[k] + ((n ∸ k) * n! / [k+1]*d[k])
    ≡˘⟨ +-distrib-/-∣ˡ _ (*-monoʳ-∣ (suc k) (k![n∸k]!∣n! k≤n)) ⟩
  ((suc k) * n! + (n ∸ k) * n!) / [k+1]*d[k]
    ≡˘⟨ cong (_/ [k+1]*d[k]) (*-distribʳ-+ (n !) (suc k) (n ∸ k)) ⟩
  ((suc k + (n ∸ k)) * n !) / [k+1]*d[k]
    ≡⟨ cong (λ z → z * n ! / [k+1]*d[k]) [k+1]+[n-k]≡[n+1] ⟩
  ((suc n) * n !) / [k+1]*d[k]
    ≡˘⟨ /-congʳ (*-assoc (suc k) (k !) ((n ∸ k) !)) ⟩
  ((suc n) * n !) / (((suc k) * k !) * (n ∸ k) !)
    ≡⟨⟩
  suc n ! / (suc k ! * (suc n ∸ suc k) !)
    ≡˘⟨ nCk≡n!/k![n-k]! [k+1]≤[n+1] ⟩
  suc n C suc k ∎
  where
    k≤n                     : k ≤ n
    k≤n                     = <⇒≤ k<n

    [k+1]≤[n+1]             : suc k ≤ suc n
    [k+1]≤[n+1]             = s≤s k≤n

    [k+1]+[n-k]≡[n+1]       : (suc k) + (n ∸ k) ≡ suc n
    [k+1]+[n-k]≡[n+1]       = m+[n∸m]≡n {suc k} [k+1]≤[n+1]

    [n-k]                   = n ∸ k
    [n-k-1]                 = n ∸ suc k

    n!                      = n !
    k!                      = k !
    [k+1]!                  = (suc k) !
    [n-k]!                  = [n-k] !
    [n-k-1]!                = [n-k-1] !

    d[k]                    = k! * [n-k]!
    [k+1]*d[k]              = (suc k) * d[k]
    d[k+1]                  = [k+1]! * [n-k-1]!
    [n-k]*d[k+1]            = [n-k] * d[k+1]
    n!/[n-k]*d[k+1]         = n ! / [n-k]*d[k+1]
    [n-k]*n!/[n-k]*d[k+1]   = [n-k] * n! / [n-k]*d[k+1]
    [n-k]*n!/[k+1]*d[k]     = [n-k] * n! / [k+1]*d[k]

    instance
      [k+1]!*[n-k]!≢0 = (suc k) !* [n-k] !≢0
      d[k]≢0          = k !* [n-k] !≢0
      d[k+1]≢0        = (suc k) !* (n ∸ suc k) !≢0
      [k+1]*d[k]≢0    = m*n≢0 (suc k) d[k]
      [n-k]≢0         = ≢-nonZero (m>n⇒m∸n≢0 k<n)
      [n-k]*d[k+1]≢0  = m*n≢0 [n-k] d[k+1]
