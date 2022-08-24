------------------------------------------------------------------------
-- The Agda standard library
--
-- Combinatorial operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Combinatorics where

open import Data.Nat.Base
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

import Data.Nat.Combinatorics.Base          as Base
import Data.Nat.Combinatorics.Specification as Specification

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
