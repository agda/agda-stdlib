------------------------------------------------------------------------
-- The Agda standard library
--
-- ℕ module n
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Mod where

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Fin.Base as F hiding (_+_; _-_)
open import Data.Fin.Relation.Unary.Top

private variable
  m n : ℕ

infixl 6 _+_ _-_

sucAbsorb : Fin n → Fin n
sucAbsorb i with view i
... | ‵fromℕ = zero
... | ‵inj₁ i = F.suc ⟦ i ⟧

predAbsorb : Fin n → Fin n
predAbsorb zero = fromℕ _
predAbsorb (F.suc i) = inject₁ i

_ℕ+_ : ℕ → Fin n → Fin n
ℕ.zero ℕ+ i = i
ℕ.suc n ℕ+ i = sucAbsorb (n ℕ+ i)

_+_ : Fin m → Fin n → Fin n
i + j = toℕ i ℕ+ j

_-_ : Fin m → Fin n → Fin m
i - j  = opposite j + i
