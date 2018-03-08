------------------------------------------------------------------------
-- The Agda standard library
--
-- The Conat type and some operations
------------------------------------------------------------------------

module Codata.Conat where

open import Size
open import Codata.Thunk

data Conat (i : Size) : Set where
  zero : Conat i
  suc : Thunk Conat i → Conat i

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

infixl 6 _+_
infixl 7 _*_

_+_ : ∀ {i} → Conat i → Conat i → Conat i
zero  + n = n
suc m + n = suc λ where .force → (m .force) + n

_*_ : ∀ {i} → Conat i → Conat i → Conat i
m     * zero  = zero
zero  * n     = zero
suc m * suc n = suc λ where .force → n .force + (m .force * suc n)
