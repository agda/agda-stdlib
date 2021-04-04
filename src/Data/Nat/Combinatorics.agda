------------------------------------------------------------------------
-- The Agda standard library
--
-- Combinatorics operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Combinatorics where

open import Data.Bool using (true; false; T)
open import Data.Nat.Base
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Data.Nat.Factorial
open import Data.Nat.Combinatorics.Base
open import Data.Nat.Combinatorics.CoreProperties
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; _≢_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; inspect; [_]; subst)

open ≤-Reasoning

private
  _!≢0 : ∀ n → False (n ! ≟ 0)
  n !≢0 = fromWitnessFalse (n!≢0 n)

  _!*_!≢0 : ∀ m n → False (m ! * n ! ≟ 0)
  m !* n !≢0 = fromWitnessFalse (m≢0∧n≢0⇒m*n≢0 (n!≢0 m) (n!≢0 n))

  ≤ᵇ⇒≤′ : ∀ {m n} → (m ≤ᵇ n) ≡ true → m ≤ n
  ≤ᵇ⇒≤′ {m} {n} eq = ≤ᵇ⇒≤ m n (subst T (sym eq) _)

  -- This proof should really live in `Data.Nat.DivMod` but
  -- the dependences between this and `Data.Nat.Divisibility` are so
  -- messed up that it's impossible at the moment. Until it's sorted
  -- out it'll live here.
  m/n/o≡m/[n*o] : ∀ {m} n o {n≢0} {o≢0} {no≢0} → n * o ∣ m →
                  ((m / n) {n≢0} / o) {o≢0} ≡ (m / (n * o)) {no≢0}
  m/n/o≡m/[n*o] {m} n@(suc _) o@(suc _) n*o∣m = *-cancelˡ-≡ (pred (n * o)) (begin-equality
    (n * o) * (m / n / o)   ≡⟨ *-assoc n o _ ⟩
    n * (o * (m / n / o))   ≡⟨ cong (n *_) (m*[n/m]≡n (m*n∣o⇒n∣o/m n o n*o∣m)) ⟩
    n * (m / n)             ≡⟨ m*[n/m]≡n (m*n∣⇒m∣ n o n*o∣m) ⟩
    m                       ≡˘⟨ m*[n/m]≡n n*o∣m ⟩
    (n * o) * (m / (n * o)) ∎)
    where open ≤-Reasoning

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

open import Data.Nat.Combinatorics.Base public
  using (_P_; _C_)

------------------------------------------------------------------------
-- Properties of _P_
------------------------------------------------------------------------
-- Spec

k≤n⇒nPk≡n!/[n∸k]! : ∀ {n k} → k ≤ n → n P k ≡ (n ! / (n ∸ k) !) {(n ∸ k) !≢0}
k≤n⇒nPk≡n!/[n∸k]! {n} {k} k≤n with k ≤ᵇ n | inspect (k ≤ᵇ_) n
... | true  | _        = nP′k≡n!/[n∸k]! k≤n
... | false | [ k≰ᵇn ] = contradiction (≤⇒≤ᵇ k≤n) (subst T k≰ᵇn)

k>n⇒nPk≡0 : ∀ {n k} → k > n → n P k ≡ 0
k>n⇒nPk≡0 {n} {k} k>n with k ≤ᵇ n | inspect (k ≤ᵇ_) n
... | true  | [ k≤ᵇn ] = contradiction (≤ᵇ⇒≤′ k≤ᵇn) (<⇒≱ k>n)
... | false | _        = refl

------------------------------------------------------------------------
-- Properties derived from spec

nPn≡n! : ∀ n → n P n ≡ n !
nPn≡n! n = begin-equality
  n P n           ≡⟨ k≤n⇒nPk≡n!/[n∸k]! (≤-refl {n}) ⟩
  n ! / (n ∸ n) ! ≡⟨ /-congʳ (cong _! (n∸n≡0 n)) ⟩
  n ! / 0 !       ≡⟨⟩
  n ! / 1         ≡⟨ n/1≡n (n !) ⟩
  n !             ∎

------------------------------------------------------------------------
-- Properties of _C_
------------------------------------------------------------------------
-- Spec

k≤n⇒nCk≡n!/k![n-k]! : ∀ {n k} → k ≤ n → n C k ≡ n ! / (k ! * (n ∸ k) !)
k≤n⇒nCk≡n!/k![n-k]! {n} {k} k≤n with k ≤ᵇ n | inspect (k ≤ᵇ_) n
... | false | [ k≰ᵇn ] = contradiction (≤⇒≤ᵇ k≤n) (subst T k≰ᵇn)
... | true  | _        with ⊓-sel k (n ∸ k)
...   | inj₁ eq rewrite eq = nC′k≡n!/k![n-k]! k≤n
...   | inj₂ eq rewrite eq = trans (C′-sym k≤n) (nC′k≡n!/k![n-k]! k≤n)

k>n⇒nCk≡0 : ∀ {n k} → k > n → n C k ≡ 0
k>n⇒nCk≡0 {n} {k} k>n with k ≤ᵇ n | inspect (k ≤ᵇ_) n
... | true  | [ k≤ᵇn ] = contradiction (≤ᵇ⇒≤′ k≤ᵇn) (<⇒≱ k>n)
... | false | _        = refl

------------------------------------------------------------------------
-- Properties derived from spec

nCk≡nC[n∸k] : ∀ {n k} → k ≤ n → n C k ≡ n C (n ∸ k)
nCk≡nC[n∸k] {n} {k} k≤n = begin-equality
  n C k                               ≡⟨ k≤n⇒nCk≡n!/k![n-k]! k≤n ⟩
  n ! / (k ! * (n ∸ k) !)             ≡˘⟨ /-congʳ {n≢0 = (n ∸ k) !* k !≢0} (*-comm ((n ∸ k) !) (k !)) ⟩
  n ! / ((n ∸ k) ! * k !)             ≡˘⟨ /-congʳ (cong ((n ∸ k) ! *_) (cong _! (m∸[m∸n]≡n k≤n))) ⟩
  n ! / ((n ∸ k) ! * (n ∸ (n ∸ k)) !) ≡˘⟨ k≤n⇒nCk≡n!/k![n-k]! (m≤n⇒n∸m≤n k≤n) ⟩
  n C (n ∸ k)                         ∎

nCk≡nPk/k! : ∀ {n k} → k ≤ n → n C k ≡ (n P k / k !) {k !≢0}
nCk≡nPk/k! {n} {k} k≤n = begin-equality
  n C k                   ≡⟨ k≤n⇒nCk≡n!/k![n-k]! k≤n ⟩
  n ! / (k ! * (n ∸ k) !) ≡˘⟨ /-congʳ {n≢0 = (n ∸ k) !* k !≢0} (*-comm ((n ∸ k)!) (k !)) ⟩
  n ! / ((n ∸ k) ! * k !) ≡˘⟨ m/n/o≡m/[n*o] ((n ∸ k) !) (k !) ([n∸k]!k!∣n! k≤n) ⟩
  (n ! / (n ∸ k) !) / k ! ≡˘⟨ /-congˡ {o≢0 = k !≢0} (k≤n⇒nPk≡n!/[n∸k]! k≤n) ⟩
  (n P k) / k !           ∎

nCn≡1 : ∀ n → n C n ≡ 1
nCn≡1 n = begin-equality
  n C n          ≡⟨ nCk≡nPk/k! (≤-refl {n}) ⟩
  (n P n) / n !  ≡⟨ /-congˡ {o≢0 = n !≢0} (nPn≡n! n) ⟩
  n ! / n !      ≡⟨ n/n≡1 (n !) ⟩
  1              ∎
