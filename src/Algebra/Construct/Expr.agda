{-# OPTIONS --without-K --safe #-}

-- This module provides the basic expression type for polynomials.

module Algebra.Construct.Expr where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

infixl 6 _⊕_
infixl 7 _⊗_
infixr 8 _⊛_
data Expr  {ℓ} (A : Set ℓ) (n : ℕ) : Set ℓ where
  Κ   : A → Expr A n
  Ι   : Fin n → Expr A n
  _⊕_ : Expr A n → Expr A n → Expr A n
  _⊗_ : Expr A n → Expr A n → Expr A n
  _⊛_ : Expr A n → ℕ → Expr A n
  ⊝_  : Expr A n → Expr A n

open import Algebra.Construct.Polynomial.Parameters

module Eval {r₁ r₂ r₃} (homo : Homomorphism r₁ r₂ r₃) where
  open Homomorphism homo
  open import Algebra.Operations.Ring.Compact rawRing

  open import Data.Vec as Vec using (Vec)

  ⟦_⟧ : ∀ {n} → Expr Raw.Carrier n → Vec Carrier n → Carrier
  ⟦ Κ x ⟧ ρ = ⟦ x ⟧ᵣ
  ⟦ Ι x ⟧ ρ = Vec.lookup ρ x
  ⟦ x ⊕ y ⟧ ρ = ⟦ x ⟧ ρ + ⟦ y ⟧ ρ
  ⟦ x ⊗ y ⟧ ρ = ⟦ x ⟧ ρ * ⟦ y ⟧ ρ
  ⟦ ⊝ x ⟧ ρ = - ⟦ x ⟧ ρ
  ⟦ x ⊛ i ⟧ ρ = ⟦ x ⟧ ρ ^ i
