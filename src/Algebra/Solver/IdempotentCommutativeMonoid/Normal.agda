------------------------------------------------------------------------
-- The Agda standard library
--
-- Solver for equations in idempotent commutative monoids
--
-- Adapted from Algebra.Solver.CommutativeMonoid
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (IdempotentCommutativeMonoid)

module Algebra.Solver.IdempotentCommutativeMonoid.Normal
  {c ℓ} (M : IdempotentCommutativeMonoid c ℓ) where

import Algebra.Properties.CommutativeSemigroup as CSProperties
open import Algebra.Properties.IdempotentCommutativeMonoid M using (∙-distrˡ-∙)
open import Data.Bool as Bool using (Bool; true; false; if_then_else_; _∨_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; replicate; zipWith)
import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise
open import Relation.Binary.Definitions using (DecidableEquality)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Relation.Nullary.Decidable       as Dec

open IdempotentCommutativeMonoid M
open CSProperties commutativeSemigroup using (x∙yz≈xy∙z; x∙yz≈y∙xz)
open ≈-Reasoning setoid

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Monoid expressions

open import Algebra.Solver.Monoid.Expression rawMonoid public
  hiding (NormalAPI)

------------------------------------------------------------------------
-- Normal forms

-- A normal form is a vector of bits (a set).

Normal : ℕ → Set
Normal n = Vec Bool n

-- The semantics of a normal form.

⟦_⟧⇓ : Normal n → Env n → Carrier
⟦ []    ⟧⇓ _ = ε
⟦ b ∷ v ⟧⇓ (a ∷ ρ) = if b then a ∙ (⟦ v ⟧⇓ ρ) else (⟦ v ⟧⇓ ρ)

-- We can decide if two normal forms are /syntactically/ equal.

infix 5 _≟_

_≟_ : DecidableEquality (Normal n)
nf₁ ≟ nf₂ = Dec.map Pointwise-≡↔≡ (decidable Bool._≟_ nf₁ nf₂)
  where open Pointwise using (Pointwise-≡↔≡; decidable)

------------------------------------------------------------------------
-- Constructions on normal forms

-- The empty set.

empty : Normal n
empty = replicate _ false

-- A singleton set.

singleton : (i : Fin n) → Normal n
singleton zero    = true ∷ empty
singleton (suc i) = false ∷ singleton i

-- The composition of normal forms.
infixr 10 _•_

_•_ : (v w : Normal n) → Normal n
_•_ = zipWith _∨_

------------------------------------------------------------------------
-- Correctness of the constructions on normal forms

-- The empty set stands for the unit ε.

empty-correct : (ρ : Env n) → ⟦ empty ⟧⇓ ρ ≈ ε
empty-correct []      = refl
empty-correct (a ∷ ρ) = empty-correct ρ

-- The singleton set stands for a single variable.

singleton-correct : (x : Fin n) (ρ : Env n) →
                    ⟦ singleton x ⟧⇓ ρ ≈ lookup ρ x
singleton-correct zero (x ∷ ρ) = begin
    x ∙ ⟦ empty ⟧⇓ ρ   ≈⟨ ∙-congˡ (empty-correct ρ) ⟩
    x ∙ ε              ≈⟨ identityʳ _ ⟩
    x                  ∎
singleton-correct (suc x) (m ∷ ρ) = singleton-correct x ρ

-- Normal form composition corresponds to the composition of the monoid.

comp-correct : ∀ v w (ρ : Env n) →
               ⟦ v • w ⟧⇓ ρ ≈ (⟦ v ⟧⇓ ρ ∙ ⟦ w ⟧⇓ ρ)
comp-correct [] [] ρ = sym (identityˡ _)
comp-correct (true ∷ v) (true ∷ w) (a ∷ ρ) =
  trans (∙-congˡ (comp-correct v w ρ)) (∙-distrˡ-∙ _ _ _)
comp-correct (true ∷ v) (false ∷ w) (a ∷ ρ) =
  trans (∙-congˡ (comp-correct v w ρ)) (x∙yz≈xy∙z _ _ _)
comp-correct (false ∷ v) (true ∷ w) (a ∷ ρ) =
  trans (∙-congˡ (comp-correct v w ρ)) (x∙yz≈y∙xz _ _ _)
comp-correct (false ∷ v) (false ∷ w) (a ∷ ρ) =
  comp-correct v w ρ

------------------------------------------------------------------------
-- Normalization

-- A normaliser.

normalise : Expr n → Normal n
normalise (var x)   = singleton x
normalise id        = empty
normalise (e₁ ⊕ e₂) = normalise e₁ • normalise e₂

-- The normaliser preserves the semantics of the expression.

correct : ∀ e ρ → ⟦ normalise {n = n} e ⟧⇓ ρ ≈ ⟦ e ⟧ ρ
correct (var x)   ρ = singleton-correct x ρ
correct id        ρ = empty-correct ρ
correct (e₁ ⊕ e₂) ρ = begin
  ⟦ normalise e₁ • normalise e₂ ⟧⇓ ρ
    ≈⟨ comp-correct (normalise e₁) (normalise e₂) ρ ⟩
  ⟦ normalise e₁ ⟧⇓ ρ ∙ ⟦ normalise e₂ ⟧⇓ ρ
    ≈⟨ ∙-cong (correct e₁ ρ) (correct e₂ ρ) ⟩
  ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ
    ∎


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.2

flip12 = x∙yz≈y∙xz
{-# WARNING_ON_USAGE flip12
"Warning: flip12 was deprecated in v2.2.
Please use Algebra.Properties.CommutativeSemigroup.x∙yz≈y∙xz instead."
#-}
distr = ∙-distrˡ-∙
{-# WARNING_ON_USAGE distr
"Warning: distr was deprecated in v2.2.
Please use Algebra.Properties.IdempotentCommutativeMonoid.∙-distrˡ-∙ instead."
#-}
sg = singleton
{-# WARNING_ON_USAGE sg
"Warning: sg was deprecated in v2.2.
Please use singleton instead."
#-}
sg-correct = singleton-correct
{-# WARNING_ON_USAGE sg-correct
"Warning: sg-correct was deprecated in v2.2.
Please use singleton-correct instead."
#-}
