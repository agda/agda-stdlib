------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties for Conats
------------------------------------------------------------------------

{-# OPTIONS --without-K --sized-types #-}

module Codata.Sized.Conat.Properties where

open import Codata.Sized.Conat
open import Codata.Sized.Conat.Bisimilarity using (_⊢_≈_; refl; zero; suc)
open import Codata.Sized.Thunk using (Thunk; Thunk^R; force)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function.Base using (_∋_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable.Core using (yes; no; map′)
open import Relation.Nullary.Negation.Core using (¬_)
open import Size using (Size)

private
  variable
    i : Size

0∸m≈0 : ∀ m → i ⊢ zero ∸ m ≈ zero
0∸m≈0 zero    = refl
0∸m≈0 (suc m) = 0∸m≈0 m

sℕ≤s⁻¹ : ∀ {m n} → suc m ℕ≤ suc n → m ℕ≤ n .force
sℕ≤s⁻¹ (sℕ≤s p) = p

infix 4 _ℕ≤?_

_ℕ≤?_ : Decidable _ℕ≤_
zero  ℕ≤? n     = yes zℕ≤n
suc m ℕ≤? zero  = no (λ ())
suc m ℕ≤? suc n = map′ sℕ≤s sℕ≤s⁻¹ (m ℕ≤? n .force)

0ℕ+-identity : ∀ {n} → i ⊢ 0 ℕ+ n ≈ n
0ℕ+-identity = refl

+ℕ0-identity : ∀ {n} → i ⊢ n +ℕ 0 ≈ n
+ℕ0-identity {n = zero}  = zero
+ℕ0-identity {n = suc n} = suc λ where .force → +ℕ0-identity
