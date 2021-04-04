------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties of combinatorics operations
------------------------------------------------------------------------
-- This module should not be imported directly! Please use
-- `Data.Nat.Combinatorics` instead.

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Combinatorics.CoreProperties where

open import Data.Bool using (true; false)
open import Data.Nat.Base
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Nat.Factorial
open import Data.Nat.Combinatorics.Base
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; _≢_)
import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as *-CS
import Algebra.Properties.CommutativeSemigroup +-commutativeSemigroup as +-CS
open import Relation.Nullary using (yes; no; does)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (subst; refl; sym; cong; cong₂)

------------------------------------------------------------------------
-- Prelude

private
  _!≢0 : ∀ n → False (n ! ≟ 0)
  n !≢0 = fromWitnessFalse (n!≢0 n)

  _!*_!≢0 : ∀ m n → False (m ! * n ! ≟ 0)
  m !* n !≢0 = fromWitnessFalse (m≢0∧n≢0⇒m*n≢0 (n!≢0 m) (n!≢0 n))

  -- This proof should really live in `Data.Nat.DivMod` but
  -- the dependences between this and `Data.Nat.Divisibility` are so
  -- messed up that it's impossible at the moment. Until it's sorted
  -- out it'll live here.
  m/n/o≡m/[n*o] : ∀ {m n o} {n≢0} {o≢0} {no≢0} → n * o ∣ m →
                  ((m / n) {n≢0} / o) {o≢0} ≡ (m / (n * o)) {no≢0}
  m/n/o≡m/[n*o] {m} n@{suc _} o@{suc _} n*o∣m = *-cancelˡ-≡ (pred (n * o)) (begin-equality
    (n * o) * (m / n / o)   ≡⟨ *-assoc n o _ ⟩
    n * (o * (m / n / o))   ≡⟨ cong (n *_) (m*[n/m]≡n (m*n∣o⇒n∣o/m n o n*o∣m)) ⟩
    n * (m / n)             ≡⟨ m*[n/m]≡n (m*n∣⇒m∣ n o n*o∣m) ⟩
    m                       ≡˘⟨ m*[n/m]≡n n*o∣m ⟩
    (n * o) * (m / (n * o)) ∎)
    where open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of _P′_

nP′k≡n!/[n∸k]! : ∀ {n k} → k ≤ n → n P′ k ≡ (n ! / (n ∸ k) !) {(n ∸ k) !≢0}
nP′k≡n!/[n∸k]! {n} {zero}  z≤n       = sym (n/n≡1 (n !))
nP′k≡n!/[n∸k]! {n} {suc k} k<n with m<n⇒0<n∸m k<n
... | n∸k>0 = begin-equality
  (n ∸ k) * (n P′ k)             ≡⟨ cong ((n ∸ k) *_) (nP′k≡n!/[n∸k]! (<⇒≤ k<n)) ⟩
  (n ∸ k) * (( n ! / (n ∸ k) !)) ≡˘⟨ *-/-assoc (n ∸ k) (m≤n⇒m!∣n! (m∸n≤m n k)) ⟩
  ((n ∸ k) * n !) / (n ∸ k) !    ≡⟨ mn/m!≡n/[m∸1]! (n ∸ k) (n !) {{>-nonZero n∸k>0}} ⟩
  n ! / (pred (n ∸ k) !)         ≡⟨ /-congʳ (cong _! (pred[m∸n]≡m∸[1+n] n k)) ⟩
  n ! / (n ∸ suc k) !            ∎
  where open ≤-Reasoning

nP′k≡n[n∸1P′k∸1] : ∀ n k → {NonZero n} → {NonZero k} → n P′ k ≡ n * (pred n P′ pred k)
nP′k≡n[n∸1P′k∸1] n           (suc zero) = refl
nP′k≡n[n∸1P′k∸1] n@(suc n-1) k@(suc k-1@(suc k-2))    = begin-equality
  n P′ k                        ≡⟨⟩
  (n ∸ k-1) * n P′ k-1          ≡⟨ cong ((n ∸ k-1) *_) (nP′k≡n[n∸1P′k∸1] n k-1) ⟩
  (n ∸ k-1) * (n * n-1 P′ k-2)  ≡⟨ x∙yz≈y∙xz (n ∸ k-1) n (n-1 P′ k-2) ⟩
  n * ((n ∸ k-1) * n-1 P′ k-2)  ≡⟨⟩
  n * n-1 P′ k-1                ∎
  where open ≤-Reasoning; open *-CS

P′-rec : ∀ {n k} → k ≤ n → {NonZero k} →
        n P′ k ≡ k * (pred n P′ pred k) + pred n P′ k
P′-rec n@{suc n-1} k@{suc k-1} k≤n = begin-equality
  n P′ k                                      ≡⟨ nP′k≡n[n∸1P′k∸1] n k ⟩
  n * n-1 P′ k-1                              ≡˘⟨ cong (_* n-1 P′ k-1) (m+[n∸m]≡n {k} {n} k≤n) ⟩
  (k + (n ∸ k)) * n-1 P′ k-1                  ≡⟨ *-distribʳ-+ (n-1 P′ k-1) k (n ∸ k) ⟩
  k * (n-1 P′ k-1) + (n-1 ∸ k-1) * n-1 P′ k-1 ≡⟨⟩
  k * (n-1 P′ k-1) + n-1 P′ k                 ∎
  where open ≤-Reasoning

nP′n≡n! : ∀ n → n P′ n ≡ n !
nP′n≡n! n = begin-equality
  n P′ n          ≡⟨ nP′k≡n!/[n∸k]! (≤-refl {n}) ⟩
  n ! / (n ∸ n) ! ≡⟨ /-congʳ (cong _! (n∸n≡0 n)) ⟩
  n ! / 0 !       ≡⟨⟩
  n ! / 1         ≡⟨ n/1≡n (n !) ⟩
  n !             ∎
  where open ≤-Reasoning

k!∣nP′k : ∀ {n k} → k ≤ n → k ! ∣ n P′ k
k!∣nP′k {n}         {zero}      k≤n = ∣-refl
k!∣nP′k n@{suc n-1} k@{suc k-1} k≤n@(s≤s k-1≤n-1) with k-1 ≟ n-1
... | yes refl = ∣-reflexive (sym (nP′n≡n! n))
... | no  k≢n  = begin
  k !                           ≡⟨⟩
  k * k-1 !                     ∣⟨ ∣m∣n⇒∣m+n (*-monoʳ-∣ k (k!∣nP′k k-1≤n-1)) ( k!∣nP′k {n-1} {k} (≤∧≢⇒< k-1≤n-1 k≢n)) ⟩
  k * (n-1 P′ k-1) + (n-1 P′ k) ≡˘⟨ P′-rec k≤n ⟩
  n P′ k                        ∎
  where open ∣-Reasoning

[n∸k]!k!∣n! : ∀ {n k} → k ≤ n → (n ∸ k) ! * k ! ∣ n !
[n∸k]!k!∣n! {n} {k} k≤n = m∣n/o⇒o*m∣n (m≤n⇒m!∣n! (m∸n≤m n k))
  (subst (k ! ∣_) (nP′k≡n!/[n∸k]! k≤n) (k!∣nP′k k≤n))

------------------------------------------------------------------------
-- Properties of _C′_

nC′k≡n!/k![n-k]! : ∀ {n k} → k ≤ n → n C′ k ≡ (n ! / (k ! * (n ∸ k) !)) {k !* (n ∸ k) !≢0}
nC′k≡n!/k![n-k]! {n} {k} k≤n = begin-equality
  n C′ k                  ≡⟨⟩
  (n P′ k) / k !          ≡⟨ /-congˡ {o≢0 = k !≢0} (nP′k≡n!/[n∸k]! k≤n) ⟩
  (n ! / (n ∸ k) !) / k ! ≡⟨ m/n/o≡m/[n*o] {n !} {(n ∸ k) !} {k !} ([n∸k]!k!∣n! k≤n) ⟩
  n ! / ((n ∸ k) ! * k !) ≡⟨ /-congʳ {n≢0 = (n ∸ k) !* k !≢0} (*-comm ((n ∸ k)!) (k !)) ⟩
  n ! / (k ! * (n ∸ k) !) ∎
  where open ≤-Reasoning

C′-sym : ∀ {n k} → k ≤ n → n C′ (n ∸ k) ≡ n C′ k
C′-sym {n} {k} k≤n = begin-equality
  n C′ (n ∸ k)                        ≡⟨ nC′k≡n!/k![n-k]! {n} {n ∸ k} (m≤n⇒n∸m≤n k≤n) ⟩
  n ! / ((n ∸ k) ! * (n ∸ (n ∸ k)) !) ≡⟨ /-congʳ (cong ((n ∸ k) ! *_) (cong _! (m∸[m∸n]≡n k≤n))) ⟩
  n ! / ((n ∸ k) ! * k !)             ≡⟨ /-congʳ {n≢0 = (n ∸ k) !* k !≢0} (*-comm ((n ∸ k) !) (k !)) ⟩
  n ! / (k ! * (n ∸ k) !)             ≡˘⟨ nC′k≡n!/k![n-k]! k≤n ⟩
  n C′ k                              ∎
  where open ≤-Reasoning
