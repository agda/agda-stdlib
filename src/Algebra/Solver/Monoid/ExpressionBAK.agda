------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for equations over monoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles.Raw using (RawMonoid)

module Algebra.Solver.Monoid.ExpressionBAK {c ℓ} (M : RawMonoid c ℓ) where

open import Algebra.Morphism.Structures using (IsMonoidHomomorphism)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base as Maybe using (Maybe)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec; lookup)
open import Level using (suc; _⊔_)
open import Relation.Binary.Consequences using (dec⇒weaklyDec)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

private
  variable
    n : ℕ

  module M = RawMonoid M


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
Env n = Vec M.Carrier n

-- The semantics of an expression is a function from an environment to
-- a value.

⟦_⟧ : Expr n → Env n → M.Carrier
⟦ var x   ⟧ ρ = lookup ρ x
⟦ id      ⟧ ρ = M.ε
⟦ e₁ ⊕ e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ M.∙ ⟦ e₂ ⟧ ρ

------------------------------------------------------------------------
-- API for normal expressions

record Normal {a r} : Set (suc (a ⊔ r) ⊔ c ⊔ ℓ) where
  infix 5 _≟_

  field

    NF        : ℕ → RawMonoid a r

  private
    N : ℕ → Set a
    N n = RawMonoid.Carrier (NF n)

  field

    ⟦var_⟧    : Fin n → N n

-- We can decide if two normal forms are /syntactically/ equal.

    _≟_       : DecidableEquality (N n)

-- The semantics of a normal form.
    ⟦_⟧⇓      : N n → Env n → M.Carrier

    ⟦var_⟧⇓   : ∀ x ρ → ⟦ ⟦var x ⟧ ⟧⇓ ρ M.≈ lookup {n = n} ρ x

    ⟦_⟧⇓-homo : ∀ ρ → IsMonoidHomomorphism (NF n) M λ e → ⟦ e ⟧⇓ ρ

-- A normaliser.

  module _ {n} where

    open RawMonoid (NF n)

    normalise : Expr n → N n
    normalise (var x)   = ⟦var x ⟧
    normalise id        = ε
    normalise (e₁ ⊕ e₂) = (normalise e₁) ∙ (normalise e₂)

    _semi≟_ : ∀ e₁ e₂ → Maybe (normalise e₁ ≡ normalise e₂)
    e₁ semi≟ e₂ = dec⇒weaklyDec _≟_ (normalise e₁) (normalise e₂)
