------------------------------------------------------------------------
-- The Agda standard library
--
-- Normal forms in commutative monoids
--
-- Adapted from Algebra.Solver.Monoid.Normal
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (CommutativeMonoid)

module Algebra.Solver.CommutativeMonoid.Normal {c ℓ} (M : CommutativeMonoid c ℓ) where

import Algebra.Properties.CommutativeSemigroup as CSProperties
  using (medial)
import Algebra.Properties.Monoid.Mult as MultProperties
  using (_×_; ×-homo-1; ×-homo-+)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; replicate; zipWith)
import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise
  using (Pointwise; _∷_; []; Pointwise-≡↔≡; decidable)
open import Relation.Binary.Definitions using (DecidableEquality)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Relation.Nullary.Decidable as Dec using (map)

open CommutativeMonoid M
open MultProperties monoid using (_×_; ×-homo-1; ×-homo-+)
open CSProperties commutativeSemigroup using (medial)
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

-- A normal form is a vector of multiplicities (a bag).

Normal : ℕ → Set
Normal n = Vec ℕ n

-- The semantics of a normal form.

⟦_⟧⇓ : Normal n → Env n → Carrier
⟦ []    ⟧⇓ _       = ε
⟦ n ∷ v ⟧⇓ (a ∷ ρ) = (n × a) ∙ (⟦ v ⟧⇓ ρ)

-- We can decide if two normal forms are /syntactically/ equal.

infix 5 _≟_

_≟_ : DecidableEquality (Normal n)
nf₁ ≟ nf₂ = Dec.map Pointwise-≡↔≡ (decidable ℕ._≟_ nf₁ nf₂)
  where open Pointwise using (Pointwise-≡↔≡; decidable)

------------------------------------------------------------------------
-- Constructions on normal forms

-- The empty bag.

empty : Normal n
empty = replicate _ 0

-- A singleton bag.

singleton : (i : Fin n) → Normal n
singleton zero    = 1 ∷ empty
singleton (suc i) = 0 ∷ singleton i

-- The composition of normal forms.
infixr 10 _•_

_•_  : (v w : Normal n) → Normal n
_•_ = zipWith _+_

------------------------------------------------------------------------
-- Correctness of the constructions on normal forms

-- The empty bag stands for the unit ε.

empty-correct : (ρ : Env n) → ⟦ empty ⟧⇓ ρ ≈ ε
empty-correct [] = refl
empty-correct (a ∷ ρ) = begin
    ε ∙ ⟦ empty ⟧⇓ ρ   ≈⟨ identityˡ _ ⟩
    ⟦ empty ⟧⇓ ρ       ≈⟨ empty-correct ρ ⟩
    ε                  ∎

-- The singleton bag stands for a single variable.

singleton-correct : (x : Fin n) (ρ : Env n) →
                    ⟦ singleton x ⟧⇓ ρ ≈ lookup ρ x
singleton-correct zero (x ∷ ρ) = begin
    (1 × x) ∙ ⟦ empty ⟧⇓ ρ   ≈⟨ ∙-congʳ (×-homo-1 _) ⟩
    x ∙ ⟦ empty ⟧⇓ ρ         ≈⟨ ∙-congˡ (empty-correct ρ) ⟩
    x ∙ ε                    ≈⟨ identityʳ _ ⟩
    x                        ∎
singleton-correct (suc x) (m ∷ ρ) = begin
    ε ∙ ⟦ singleton x ⟧⇓ ρ   ≈⟨ identityˡ _ ⟩
    ⟦ singleton x ⟧⇓ ρ       ≈⟨ singleton-correct x ρ ⟩
    lookup ρ x        ∎

-- Normal form composition corresponds to the composition of the monoid.

comp-correct : ∀ v w (ρ : Env n) →
               ⟦ v • w ⟧⇓ ρ ≈ (⟦ v ⟧⇓ ρ ∙ ⟦ w ⟧⇓ ρ)
comp-correct [] [] _ =  sym (identityˡ _)
comp-correct (l ∷ v) (m ∷ w) (a ∷ ρ) = begin
  ((l + m) × a) ∙ ⟦ v • w ⟧⇓ ρ              ≈⟨ ∙-congʳ  (×-homo-+ a l m) ⟩
  (l × a) ∙ (m × a) ∙ ⟦ v • w ⟧⇓ ρ          ≈⟨ ∙-congˡ  (comp-correct v w ρ) ⟩
  (l × a) ∙ (m × a) ∙ (⟦ v ⟧⇓ ρ ∙ ⟦ w ⟧⇓ ρ) ≈⟨ medial _ _ _ _ ⟩
  ⟦ l ∷ v ⟧⇓ (a ∷ ρ) ∙ ⟦ m ∷ w ⟧⇓ (a ∷ ρ)   ∎

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
