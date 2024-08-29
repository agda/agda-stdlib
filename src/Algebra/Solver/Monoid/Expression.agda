------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for equations over monoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles.Raw using (RawMonoid)

module Algebra.Solver.Monoid.Expression {c ℓ} (M : RawMonoid c ℓ) where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec; lookup)
open import Level using (suc; _⊔_)
open import Relation.Binary.Definitions using (DecidableEquality)

open RawMonoid M

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Monoid expressions

-- There is one constructor for every operation, plus one for
-- variables; there may be at most n variables.

infixr 5 _⊕_

data Expr (n : ℕ) : Set where
  var : Fin n → Expr n
  id  : Expr n
  _⊕_ : Expr n → Expr n → Expr n

-- An environment contains one value for every variable.

Env : ℕ → Set _
Env n = Vec Carrier n

-- The semantics of an expression is a function from an environment to
-- a value.

⟦_⟧ : Expr n → Env n → Carrier
⟦ var x   ⟧ ρ = lookup ρ x
⟦ id      ⟧ ρ = ε
⟦ e₁ ⊕ e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ

------------------------------------------------------------------------
-- API for normal expressions

record NormalAPI a : Set (suc a ⊔ c ⊔ ℓ) where
  infix 5 _≟_

  field

-- The type of normal forms.
    Normal    : ℕ → Set a
-- We can decide if two normal forms are /syntactically/ equal.
    _≟_       : DecidableEquality (Normal n)
-- A normaliser.
    normalise : Expr n → Normal n
-- The semantics of a normal form.
    ⟦_⟧⇓      : Normal n → Env n → Carrier
-- The normaliser preserves the semantics of the expression.
    correct   : ∀ e ρ → ⟦ normalise {n = n} e ⟧⇓ ρ ≈ ⟦ e ⟧ ρ

