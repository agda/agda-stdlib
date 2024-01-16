------------------------------------------------------------------------
-- The Agda standard library
--
-- ℕ module n
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Mod where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base
  using (Fin; zero; suc; toℕ; fromℕ; inject₁; opposite)
open import Data.Fin.Relation.Unary.Top

private variable
  m n : ℕ

infixl 6 _+_ _-_

sucMod : Fin n → Fin n
sucMod i with view i
... | ‵fromℕ = zero
... | ‵inj₁ i = suc ⟦ i ⟧

predMod : Fin n → Fin n
predMod zero = fromℕ _
predMod (suc i) = inject₁ i

_ℕ+_ : ℕ → Fin n → Fin n
zero  ℕ+ i = i
suc n ℕ+ i = sucMod (n ℕ+ i)

_+_ : Fin n → Fin m → Fin n
i + j = toℕ j ℕ+ i

_-_ : Fin n → Fin m → Fin n
i - j  = i + opposite j
