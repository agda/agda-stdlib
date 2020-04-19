------------------------------------------------------------------------
-- The Agda standard library
--
-- A type for expressions over a raw ring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Tactic.RingSolver.Core.Expression where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Vec.Base as Vec using (Vec)

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
  (let open RawRing rawRing)
  {a} {A : Set a} (⟦_⟧ᵣ : A → Carrier) where

  open import Algebra.Operations.Ring rawRing

  ⟦_⟧ : ∀ {n} → Expr A n → Vec Carrier n → Carrier
  ⟦ Κ x   ⟧ ρ = ⟦ x ⟧ᵣ
  ⟦ Ι x   ⟧ ρ = Vec.lookup ρ x
  ⟦ x ⊕ y ⟧ ρ = ⟦ x ⟧ ρ + ⟦ y ⟧ ρ
  ⟦ x ⊗ y ⟧ ρ = ⟦ x ⟧ ρ * ⟦ y ⟧ ρ
  ⟦   ⊝ x ⟧ ρ = - ⟦ x ⟧ ρ
  ⟦ x ⊛ i ⟧ ρ = ⟦ x ⟧ ρ ^ i
