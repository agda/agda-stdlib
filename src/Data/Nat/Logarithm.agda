------------------------------------------------------------------------
-- The Agda standard library
--
-- Logarithm base 2 and respective properties
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Nat.Logarithm where

open import Data.Nat.Base
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Logarithm.Core
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

------------------------------------------------------------------------
-- Logarithm base 2

-- Floor version

⌊log₂_⌋ : ℕ → ℕ
⌊log₂ n ⌋ = ⌊log2⌋ n (<-wellFounded n)

-- Ceil version

⌈log₂_⌉ : ℕ → ℕ
⌈log₂ n ⌉ = ⌈log2⌉ n (<-wellFounded n)

------------------------------------------------------------------------
-- Properties of ⌊log₂_⌋

⌊log₂⌋-mono-≤ : ∀ {m n} → m ≤ n → ⌊log₂ m ⌋ ≤ ⌊log₂ n ⌋
⌊log₂⌋-mono-≤ p = ⌊log2⌋-mono-≤ p

⌊log₂⌊n/2⌋⌋≡⌊log₂n⌋∸1 : ∀ n → ⌊log₂ ⌊ n /2⌋ ⌋ ≡ ⌊log₂ n ⌋ ∸ 1
⌊log₂⌊n/2⌋⌋≡⌊log₂n⌋∸1 n = ⌊log2⌋⌊n/2⌋≡⌊log2⌋n∸1 n

⌊log₂[2*b]⌋≡1+⌊log₂b⌋ : ∀ n .{{_ : NonZero n}} → ⌊log₂ (2 * n) ⌋ ≡ 1 + ⌊log₂ n ⌋
⌊log₂[2*b]⌋≡1+⌊log₂b⌋ n = ⌊log2⌋2*b≡1+⌊log2⌋b n

⌊log₂[2^n]⌋≡n : ∀ n → ⌊log₂ (2 ^ n) ⌋ ≡ n
⌊log₂[2^n]⌋≡n n = ⌊log2⌋2^n≡n n

2^⌊log₂n⌋≤n : ∀ n .{{ _ : NonZero n }} → 2 ^ ⌊log₂ n ⌋ ≤ n
2^⌊log₂n⌋≤n n = 2^⌊log2n⌋≤n n (<-wellFounded n)

------------------------------------------------------------------------
-- Properties of ⌈log₂_⌉

⌈log₂⌉-mono-≤ : ∀ {m n} → m ≤ n → ⌈log₂ m ⌉ ≤ ⌈log₂ n ⌉
⌈log₂⌉-mono-≤ p = ⌈log2⌉-mono-≤ p

⌈log₂⌈n/2⌉⌉≡⌈log₂n⌉∸1 : ∀ n → ⌈log₂ ⌈ n /2⌉ ⌉ ≡ ⌈log₂ n ⌉ ∸ 1
⌈log₂⌈n/2⌉⌉≡⌈log₂n⌉∸1 n = ⌈log2⌉⌈n/2⌉≡⌈log2⌉n∸1 n

⌈log₂2*n⌉≡1+⌈log₂n⌉ : ∀ n .{{_ : NonZero n}} → ⌈log₂ (2 * n) ⌉ ≡ 1 + ⌈log₂ n ⌉
⌈log₂2*n⌉≡1+⌈log₂n⌉ n = ⌈log2⌉2*n≡1+⌈log2⌉n n

⌈log₂2^n⌉≡n : ∀ n → ⌈log₂ (2 ^ n) ⌉ ≡ n
⌈log₂2^n⌉≡n n = ⌈log2⌉2^n≡n n

n≤2^⌈log₂n⌉ : ∀ n → n ≤ 2 ^ ⌈log₂ n ⌉
n≤2^⌈log₂n⌉ n = n≤2^⌈log2n⌉ n (<-wellFounded n)
