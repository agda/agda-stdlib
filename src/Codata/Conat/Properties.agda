------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties for Conats
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Codata.Conat.Properties where

open import Size
open import Data.Nat.Base using (ℕ; zero; suc)
open import Codata.Thunk
open import Codata.Conat
open import Codata.Conat.Bisimilarity
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable using (map′)
open import Relation.Binary

private
  variable
    i : Size

0∸m≈0 : ∀ m → i ⊢ zero ∸ m ≈ zero
0∸m≈0 zero    = refl
0∸m≈0 (suc m) = 0∸m≈0 m

sℕ≤s⁻¹ : ∀ {m n} → suc m ℕ≤ suc n → m ℕ≤ n .force
sℕ≤s⁻¹ (sℕ≤s p) = p

_ℕ≤?_ : Decidable _ℕ≤_
zero  ℕ≤? n     = yes zℕ≤n
suc m ℕ≤? zero  = no (λ ())
suc m ℕ≤? suc n = map′ sℕ≤s sℕ≤s⁻¹ (m ℕ≤? n .force)

0ℕ+-identity : ∀ {n} → i ⊢ 0 ℕ+ n ≈ n
0ℕ+-identity = refl

+ℕ0-identity : ∀ {n} → i ⊢ n +ℕ 0 ≈ n
+ℕ0-identity {n = zero}  = zero
+ℕ0-identity {n = suc n} = suc λ where .force → +ℕ0-identity
