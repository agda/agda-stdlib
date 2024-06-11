------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for equations over monoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)

module Algebra.Solver.Monoid.Normal {c ℓ} (M : Monoid c ℓ) where

open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as Fin
open import Data.List.Base using (List; [] ; _∷_; _++_)
import Data.List.Relation.Binary.Equality.DecPropositional as ≋
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (lookup)
open import Function.Base using (_∘_; _$_)
open import Relation.Binary.Definitions using (DecidableEquality)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Relation.Nullary.Decidable as Dec

open Monoid M
open ≈-Reasoning setoid

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Monoid expressions

open import Algebra.Solver.Monoid.Expression rawMonoid public

------------------------------------------------------------------------
-- Normal forms

-- A normal form is a list of variables.

Normal : ℕ → Set _
Normal n = List (Fin n)

-- The semantics of a normal form.

⟦_⟧⇓ : Normal n → Env n → Carrier
⟦ []     ⟧⇓ ρ = ε
⟦ x ∷ nf ⟧⇓ ρ = lookup ρ x ∙ ⟦ nf ⟧⇓ ρ

-- We can decide if two normal forms are /syntactically/ equal.

infix 5 _≟_

_≟_ : DecidableEquality (Normal n)
nf₁ ≟ nf₂ = Dec.map′ ≋⇒≡ ≡⇒≋ (nf₁ ≋? nf₂)
  where open ≋ Fin._≟_ using (_≋?_; ≋⇒≡; ≡⇒≋)

-- A normaliser.

normalise : Expr n → Normal n
normalise (var x)   = x ∷ []
normalise id        = []
normalise (e₁ ⊕ e₂) = normalise e₁ ++ normalise e₂

-- The normaliser is homomorphic with respect to _++_/_∙_.

comp-correct : ∀ nf₁ nf₂ (ρ : Env n) →
              ⟦ nf₁ ++ nf₂ ⟧⇓ ρ ≈ (⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ)
comp-correct [] nf₂ ρ = begin
  ⟦ nf₂ ⟧⇓ ρ      ≈⟨ identityˡ _ ⟨
  ε ∙ ⟦ nf₂ ⟧⇓ ρ  ∎
comp-correct (x ∷ nf₁) nf₂ ρ = begin
  lookup ρ x ∙ ⟦ nf₁ ++ nf₂ ⟧⇓ ρ          ≈⟨ ∙-congˡ (comp-correct nf₁ nf₂ ρ) ⟩
  lookup ρ x ∙ (⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ)  ≈⟨ assoc _ _ _ ⟨
  lookup ρ x ∙ ⟦ nf₁ ⟧⇓ ρ ∙ ⟦ nf₂ ⟧⇓ ρ    ∎

-- The normaliser preserves the semantics of the expression.

correct : ∀ e ρ → ⟦ normalise {n = n} e ⟧⇓ ρ ≈ ⟦ e ⟧ ρ
correct (var x) ρ = begin
  lookup ρ x ∙ ε  ≈⟨ identityʳ _ ⟩
  lookup ρ x      ∎
correct id ρ = begin
  ε  ∎
correct (e₁ ⊕ e₂) ρ = begin
  ⟦ normalise e₁ ++ normalise e₂ ⟧⇓ ρ        ≈⟨ comp-correct (normalise e₁) (normalise e₂) ρ ⟩
  ⟦ normalise e₁ ⟧⇓ ρ ∙ ⟦ normalise e₂ ⟧⇓ ρ  ≈⟨ ∙-cong (correct e₁ ρ) (correct e₂ ρ) ⟩
  ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ                        ∎
