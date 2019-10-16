{-# OPTIONS --without-K --safe #-}

-- This module provides a type for expressions in a ring.

module Algebra.Construct.Ring.Expr where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec as Vec using (Vec)

open import Algebra

infixl 6 _⊕_
infixl 7 _⊗_
infixr 8 _⊛_
data Expr  {ℓ} (A : Set ℓ) (n : ℕ) : Set ℓ where
  Κ   : A → Expr A n
  Ι   : Fin n → Expr A n
  _⊕_ : Expr A n → Expr A n → Expr A n
  _⊗_ : Expr A n → Expr A n → Expr A n
  _⊛_ : Expr A n → ℕ → Expr A n -- exponentiation
  ⊝_  : Expr A n → Expr A n


module Eval {ℓ₁ ℓ₂} (rawRing : RawRing ℓ₁) {A : Set ℓ₂} (⟦_⟧ᵣ : A → RawRing.Carrier rawRing) where
  open RawRing rawRing
  open import Algebra.Operations.Ring.Compact rawRing

  ⟦_⟧ : ∀ {n} → Expr A n → Vec Carrier n → Carrier
  ⟦ Κ x ⟧ ρ = ⟦ x ⟧ᵣ
  ⟦ Ι x ⟧ ρ = Vec.lookup ρ x
  ⟦ x ⊕ y ⟧ ρ = ⟦ x ⟧ ρ + ⟦ y ⟧ ρ
  ⟦ x ⊗ y ⟧ ρ = ⟦ x ⟧ ρ * ⟦ y ⟧ ρ
  ⟦ ⊝ x ⟧ ρ = - ⟦ x ⟧ ρ
  ⟦ x ⊛ i ⟧ ρ = ⟦ x ⟧ ρ ^ i
