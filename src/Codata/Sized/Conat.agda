------------------------------------------------------------------------
-- The Agda standard library
--
-- The Conat type and some operations
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Codata.Sized.Conat where

open import Size using (Size ; ∞; Size<_)
open import Codata.Sized.Thunk using (Thunk ; force)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Relation.Nullary.Negation.Core using (¬_)

------------------------------------------------------------------------
-- Definition and first values

data Conat (i : Size) : Set where
  zero : Conat i
  suc : Thunk Conat i → Conat i

infinity : ∀ {i} → Conat i
infinity = suc λ where .force → infinity

fromℕ : ℕ → Conat ∞
fromℕ zero    = zero
fromℕ (suc n) = suc λ where .force → fromℕ n

------------------------------------------------------------------------
-- Arithmetic operations

pred : ∀ {i} {j : Size< i} → Conat i → Conat j
pred zero    = zero
pred (suc n) = n .force

infixl 6 _∸_ _+_ _ℕ+_ _+ℕ_
infixl 7 _*_

_∸_ : Conat ∞ → ℕ → Conat ∞
m ∸ zero  = m
m ∸ suc n = pred m ∸ n

_ℕ+_ : ℕ → ∀ {i} → Conat i → Conat i
zero  ℕ+ n = n
suc m ℕ+ n = suc λ where .force → m ℕ+ n

_+ℕ_ : ∀ {i} → Conat i → ℕ → Conat i
zero  +ℕ n = fromℕ n
suc m +ℕ n = suc λ where .force → (m .force) +ℕ n

_+_ : ∀ {i} → Conat i → Conat i → Conat i
zero  + n = n
suc m + n = suc λ where .force → (m .force) + n

_*_ : ∀ {i} → Conat i → Conat i → Conat i
m     * zero  = zero
zero  * n     = zero
suc m * suc n = suc λ where .force → n .force + (m .force * suc n)

-- Max and Min

infixl 6 _⊔_
infixl 7 _⊓_

_⊔_ : ∀ {i} → Conat i → Conat i → Conat i
zero  ⊔ n     = n
m     ⊔ zero  = m
suc m ⊔ suc n = suc λ where .force → m .force ⊔ n .force

_⊓_ : ∀ {i} → Conat i → Conat i → Conat i
zero  ⊓ n     = zero
m     ⊓ zero  = zero
suc m ⊓ suc n = suc λ where .force → m .force ⊓ n .force

------------------------------------------------------------------------
-- Finiteness

data Finite : Conat ∞ → Set where
  zero : Finite zero
  suc  : ∀ {n} → Finite (n .force) → Finite (suc n)

toℕ : ∀ {n} → Finite n → ℕ
toℕ zero    = zero
toℕ (suc n) = suc (toℕ n)

¬Finite∞ : ¬ (Finite infinity)
¬Finite∞ (suc p) = ¬Finite∞ p

------------------------------------------------------------------------
-- Order wrt to Nat

infix 4 _ℕ<_ _ℕ≤infinity _ℕ≤_

data _ℕ≤_ : ℕ → Conat ∞ → Set where
  zℕ≤n : ∀ {n} → zero ℕ≤ n
  sℕ≤s : ∀ {k n} → k ℕ≤ n .force → suc k ℕ≤ suc n

_ℕ<_ : ℕ → Conat ∞ → Set
k ℕ< n = suc k ℕ≤ n

_ℕ≤infinity : ∀ k → k ℕ≤ infinity
zero  ℕ≤infinity = zℕ≤n
suc k ℕ≤infinity = sℕ≤s (k ℕ≤infinity)
