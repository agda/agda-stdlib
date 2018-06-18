------------------------------------------------------------------------
-- The Agda standard library
--
-- The Conat type and some operations
------------------------------------------------------------------------

module Codata.Conat where

open import Size
open import Codata.Thunk

open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Relation.Nullary

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

infixl 6 _∸_ _+_
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
suc m ⊓ suc n = suc λ where .force → m .force ⊔ n .force

------------------------------------------------------------------------
-- Finiteness

data Finite : Conat ∞ → Set where
  zero : Finite zero
  suc  : ∀ {n} → Finite (n .force) → Finite (suc n)

extract : ∀ {n} → Finite n → ℕ
extract zero    = zero
extract (suc n) = suc (extract n)

¬Finite∞ : ¬ (Finite infinity)
¬Finite∞ (suc p) = ¬Finite∞ p
