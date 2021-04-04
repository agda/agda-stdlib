------------------------------------------------------------------------
-- The Agda standard library
--
-- Combinatorics operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Factorial where

open import Data.Nat.Base
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary.Decidable using (False; fromWitnessFalse)
open import Relation.Binary.PropositionalEquality using (refl; sym; cong)

------------------------------------------------------------------------
-- Base definition

infix  8 _!

_! : ℕ → ℕ
zero  ! = 1
suc n ! = suc n * n !

------------------------------------------------------------------------
-- Properties

1≤n! : ∀ n → 1 ≤ n !
1≤n! zero    = s≤s z≤n
1≤n! (suc n) = *-mono-≤ (s≤s (z≤n {n = n})) (1≤n! n)

n!≢0 : ∀ n → n ! ≢ 0
n!≢0 (suc n) n!≡0 = m≢0∧n≢0⇒m*n≢0 (1+n≢0 {n}) (n!≢0 n) n!≡0

private
  _!≢0 : ∀ n → False (n ! ≟ 0)
  n !≢0 = fromWitnessFalse (n!≢0 n)

m≤n⇒m!∣n! : ∀ {m n} → m ≤ n → m ! ∣ n !
m≤n⇒m!∣n! m≤n = help (≤⇒≤′ m≤n)
  where
  help : ∀ {m n} → m ≤′ n → m ! ∣ n !
  help {m} {n}     ≤′-refl        = ∣-refl
  help {m} {suc n} (≤′-step m≤′n) = ∣n⇒∣m*n (suc n) (help m≤′n)

mn/m!≡n/[m∸1]! : ∀ m n → {{.(NonZero m)}} →
                 (m * n / m !) {m !≢0}  ≡ (n / (pred m) !) {pred m !≢0}
mn/m!≡n/[m∸1]! (suc m) n = m*n/m*o≡n/o (suc m) n (m !)
