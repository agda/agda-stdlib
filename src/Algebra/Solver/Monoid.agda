------------------------------------------------------------------------
-- The Agda standard library
--
-- Solver for monoid equalities
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra

module Algebra.Solver.Monoid {m₁ m₂} (M : Monoid m₁ m₂) where

open import Data.Fin as Fin hiding (_≟_)
import Data.Fin.Properties as Fin
open import Data.List.Base hiding (lookup)
import Data.List.Relation.Binary.Equality.DecPropositional as ListEq
open import Data.Maybe as Maybe
  using (Maybe; decToMaybe; From-just; from-just)
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Vec using (Vec; lookup)
open import Function using (_∘_; _$_)
open import Relation.Binary using (Decidable)

open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Relation.Binary.Reflection
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec

open Monoid M
open import Relation.Binary.Reasoning.Setoid setoid

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

⟦_⟧ : ∀ {n} → Expr n → Env n → Carrier
⟦ var x   ⟧ ρ = lookup ρ x
⟦ id      ⟧ ρ = ε
⟦ e₁ ⊕ e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ

------------------------------------------------------------------------
-- Normal forms

-- A normal form is a list of variables.

Normal : ℕ → Set
Normal n = List (Fin n)

-- The semantics of a normal form.

⟦_⟧⇓ : ∀ {n} → Normal n → Env n → Carrier
⟦ []     ⟧⇓ ρ = ε
⟦ x ∷ nf ⟧⇓ ρ = lookup ρ x ∙ ⟦ nf ⟧⇓ ρ

-- A normaliser.

normalise : ∀ {n} → Expr n → Normal n
normalise (var x)   = x ∷ []
normalise id        = []
normalise (e₁ ⊕ e₂) = normalise e₁ ++ normalise e₂

-- The normaliser is homomorphic with respect to _++_/_∙_.

homomorphic : ∀ {n} (nf₁ nf₂ : Normal n) (ρ : Env n) →
              ⟦ nf₁ ++ nf₂ ⟧⇓ ρ ≈ (⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ)
homomorphic [] nf₂ ρ = begin
  ⟦ nf₂ ⟧⇓ ρ      ≈⟨ sym $ identityˡ _ ⟩
  ε ∙ ⟦ nf₂ ⟧⇓ ρ  ∎
homomorphic (x ∷ nf₁) nf₂ ρ = begin
  lookup ρ x ∙ ⟦ nf₁ ++ nf₂ ⟧⇓ ρ          ≈⟨ ∙-congʳ (homomorphic nf₁ nf₂ ρ) ⟩
  lookup ρ x ∙ (⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ)  ≈⟨ sym $ assoc _ _ _ ⟩
  lookup ρ x ∙ ⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ    ∎

-- The normaliser preserves the semantics of the expression.

normalise-correct :
  ∀ {n} (e : Expr n) (ρ : Env n) → ⟦ normalise e ⟧⇓ ρ ≈ ⟦ e ⟧ ρ
normalise-correct (var x) ρ = begin
  lookup ρ x ∙ ε  ≈⟨ identityʳ _ ⟩
  lookup ρ x      ∎
normalise-correct id ρ = begin
  ε  ∎
normalise-correct (e₁ ⊕ e₂) ρ = begin
  ⟦ normalise e₁ ++ normalise e₂ ⟧⇓ ρ        ≈⟨ homomorphic (normalise e₁) (normalise e₂) ρ ⟩
  ⟦ normalise e₁ ⟧⇓ ρ ∙ ⟦ normalise e₂ ⟧⇓ ρ  ≈⟨ ∙-cong (normalise-correct e₁ ρ) (normalise-correct e₂ ρ) ⟩
  ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ                        ∎

------------------------------------------------------------------------
-- "Tactics"

open module R = Relation.Binary.Reflection
                  setoid var ⟦_⟧ (⟦_⟧⇓ ∘ normalise) normalise-correct
  public using (solve; _⊜_)

-- We can decide if two normal forms are /syntactically/ equal.

infix 5 _≟_

_≟_ : ∀ {n} → Decidable {A = Normal n} _≡_
nf₁ ≟ nf₂ = Dec.map′ ≋⇒≡ ≡⇒≋ (nf₁ ≋? nf₂)
  where open ListEq Fin._≟_

-- We can also give a sound, but not necessarily complete, procedure
-- for determining if two expressions have the same semantics.

prove′ : ∀ {n} (e₁ e₂ : Expr n) → Maybe (∀ ρ → ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ)
prove′ e₁ e₂ =
  Maybe.map lemma $ decToMaybe (normalise e₁ ≟ normalise e₂)
  where
  lemma : normalise e₁ ≡ normalise e₂ → ∀ ρ → ⟦ e₁ ⟧ ρ ≈ ⟦ e₂ ⟧ ρ
  lemma eq ρ =
    R.prove ρ e₁ e₂ (begin
      ⟦ normalise e₁ ⟧⇓ ρ  ≡⟨ P.cong (λ e → ⟦ e ⟧⇓ ρ) eq ⟩
      ⟦ normalise e₂ ⟧⇓ ρ  ∎)

-- This procedure can be combined with from-just.

prove : ∀ n (es : Expr n × Expr n) →
        From-just (uncurry prove′ es)
prove _ = from-just ∘ uncurry prove′
