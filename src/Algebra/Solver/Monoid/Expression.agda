------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for equations over monoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)

module Algebra.Solver.Monoid.Expression {c ℓ} (M : Monoid c ℓ) where

open import Algebra.Bundles.Raw using (RawMonoid)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism)
open import Algebra.Structures using (IsMonoid)
open import Data.Fin.Base using (Fin)
open import Data.Maybe.Base as Maybe using (Maybe)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec; lookup)
open import Level using (suc; _⊔_)
open import Relation.Binary.Consequences using (dec⇒weaklyDec)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    n : ℕ

  module M = Monoid M


------------------------------------------------------------------------
-- Monoid expressions

-- There is one constructor for every operation, plus one for
-- variables; there may be at most n variables.

infixr 5 _‵∙_

data Expr (n : ℕ) : Set where
  ‵var : Fin n → Expr n
  ‵ε   : Expr n
  _‵∙_ : Expr n → Expr n → Expr n

-- An environment contains one value for every variable.

Env : ℕ → Set _
Env n = Vec M.Carrier n

-- The semantics of an expression is a function from an environment to
-- a value.

⟦_⟧ : Expr n → Env n → M.Carrier
⟦ ‵var x   ⟧ ρ = lookup ρ x
⟦ ‵ε       ⟧ ρ = M.ε
⟦ e₁ ‵∙ e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ M.∙ ⟦ e₂ ⟧ ρ

------------------------------------------------------------------------
-- API for normal expressions

record NormalAPI {a r} : Set (suc (a ⊔ r) ⊔ c ⊔ ℓ) where
  infix 5 _≟_

  field

    NF        : ℕ → RawMonoid a r

  private
    N : ℕ → Set a
    N n = RawMonoid.Carrier (NF n)

  field

    var       : Fin n → N n

-- We can decide if two normal forms are /syntactically/ equal.

    _≟_       : DecidableEquality (N n)

-- The semantics of a normal form.
    ⟦_⟧⇓     : N n → Env n → M.Carrier

-- Which "agrees with the environment on variables".
    ⟦var_⟧⇓  : ∀ x ρ → ⟦ var x ⟧⇓ ρ M.≈ lookup {n = n} ρ x

-- And which is a monoid homomorphism between NF and M
    ⟦⟧⇓-homo : ∀ ρ → IsMonoidHomomorphism (NF n) M.rawMonoid λ e → ⟦ e ⟧⇓ ρ

------------------------------------------------------------------------
-- The normaliser and its correctness proof, as manifest fields of `Normal`

  module _ {n} where

    open module N = RawMonoid (NF n)

-- Definition

    normalise : Expr n → N n
    normalise (‵var x)   = var x
    normalise ‵ε         = N.ε
    normalise (e₁ ‵∙ e₂) = (normalise e₁) N.∙ (normalise e₂)

-- The normaliser preserves the semantics of the expression.

    correct : ∀ e ρ → ⟦ normalise e ⟧⇓ ρ M.≈ ⟦ e ⟧ ρ
    correct (‵var x)   ρ = ⟦var x ⟧⇓ ρ
    correct ‵ε         ρ = ε-homo
      where open IsMonoidHomomorphism (⟦⟧⇓-homo ρ)
    correct (e₁ ‵∙ e₂) ρ = begin
      ⟦ normalise e₁ N.∙ normalise e₂ ⟧⇓ ρ
        ≈⟨ homo (normalise e₁) (normalise e₂) ⟩
      ⟦ normalise e₁ ⟧⇓ ρ M.∙ ⟦ normalise e₂ ⟧⇓ ρ
        ≈⟨ ∙-cong (correct e₁ ρ) (correct e₂ ρ) ⟩
      ⟦ e₁ ⟧ ρ M.∙ ⟦ e₂ ⟧ ρ
        ∎
      where
      open IsMonoid M.isMonoid using (∙-cong; setoid)
      open ≈-Reasoning setoid
      open IsMonoidHomomorphism (⟦⟧⇓-homo ρ)

-- Semi-decision procedure for equality of normalised expressions

    _semi≟_ : ∀ e₁ e₂ → Maybe (normalise e₁ ≡ normalise e₂)
    e₁ semi≟ e₂ = dec⇒weaklyDec _≟_ (normalise e₁) (normalise e₂)

