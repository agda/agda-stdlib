------------------------------------------------------------------------
-- The Agda standard library
--
-- Types and functions which are used to keep track of height
-- invariants in AVL Trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.AVL.Height where

open import Data.Nat.Base
open import Data.Fin.Base using (Fin; zero; suc)

ℕ₂ = Fin 2
pattern 0# = zero
pattern 1# = suc zero
pattern ## = suc (suc ())

-- Addition.

infixl 6 _⊕_

_⊕_ : ℕ₂ → ℕ → ℕ
0# ⊕ n = n
1# ⊕ n = 1 + n

-- pred[ i ⊕ n ] = pred (i ⊕ n).

pred[_⊕_] : ℕ₂ → ℕ → ℕ
pred[ i ⊕ zero  ] = 0
pred[ i ⊕ suc n ] = i ⊕ n

infix 4 _∼_⊔_

-- If i ∼ j ⊔ m, then the difference between i and j is at most 1,
-- and the maximum of i and j is m. _∼_⊔_ is used to record the
-- balance factor of the AVL trees, and also to ensure that the
-- absolute value of the balance factor is never more than 1.

data _∼_⊔_ : ℕ → ℕ → ℕ → Set where
  ∼+ : ∀ {n} →     n ∼ 1 + n ⊔ 1 + n
  ∼0 : ∀ {n} →     n ∼ n     ⊔ n
  ∼- : ∀ {n} → 1 + n ∼ n     ⊔ 1 + n

-- Some lemmas.

max∼ : ∀ {i j m} → i ∼ j ⊔ m → m ∼ i ⊔ m
max∼ ∼+ = ∼-
max∼ ∼0 = ∼0
max∼ ∼- = ∼0

∼max : ∀ {i j m} → i ∼ j ⊔ m → j ∼ m ⊔ m
∼max ∼+ = ∼0
∼max ∼0 = ∼0
∼max ∼- = ∼+
