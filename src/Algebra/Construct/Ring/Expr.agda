------------------------------------------------------------------------
-- The Agda standard library
--
-- This module provides a type for expressions in a ring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Construct.Ring.Expr where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Vec as Vec using (Vec)

open import Algebra

infixl 6 _⊕_
infixl 7 _⊗_
infixr 8 _⊛_

data Expr {a} (A : Set a) (n : ℕ) : Set a where
  Κ   : A → Expr A n                   -- Constant
  Ι   : Fin n → Expr A n               -- Variable
  _⊕_ : Expr A n → Expr A n → Expr A n -- Addition
  _⊗_ : Expr A n → Expr A n → Expr A n -- Multiplication
  _⊛_ : Expr A n → ℕ → Expr A n        -- Exponentiation
  ⊝_  : Expr A n → Expr A n            -- Negation


module Eval
  {ℓ₁ ℓ₂} (rawRing : RawRing ℓ₁ ℓ₂)
  {a} {A : Set a} (⟦_⟧ᵣ : A → RawRing.Carrier rawRing) where
  
  open RawRing rawRing
  open import Algebra.Operations.Ring rawRing

  ⟦_⟧ : ∀ {n} → Expr A n → Vec Carrier n → Carrier
  ⟦ Κ x   ⟧ ρ = ⟦ x ⟧ᵣ
  ⟦ Ι x   ⟧ ρ = Vec.lookup ρ x
  ⟦ x ⊕ y ⟧ ρ = ⟦ x ⟧ ρ + ⟦ y ⟧ ρ
  ⟦ x ⊗ y ⟧ ρ = ⟦ x ⟧ ρ * ⟦ y ⟧ ρ
  ⟦ ⊝ x   ⟧ ρ = - ⟦ x ⟧ ρ
  ⟦ x ⊛ i ⟧ ρ = ⟦ x ⟧ ρ ^ i
