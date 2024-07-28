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
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_)
open import Data.Nat.GeneralisedArithmetic using (fold)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; replicate; zipWith)
import Data.Vec.Relation.Binary.Pointwise.Inductive as Pointwise
open import Relation.Binary.Definitions using (DecidableEquality)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning
import Relation.Nullary.Decidable as Dec

open CommutativeMonoid M
open CSProperties commutativeSemigroup using (x∙yz≈y∙xz)
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
⟦ n ∷ v ⟧⇓ (a ∷ ρ) = fold (⟦ v ⟧⇓ ρ) (a ∙_) n

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

sg : (i : Fin n) → Normal n
sg zero    = 1 ∷ empty
sg (suc i) = 0 ∷ sg i

-- The composition of normal forms.
infixr 10 _•_

_•_  : (v w : Normal n) → Normal n
_•_ = zipWith _+_

------------------------------------------------------------------------
-- Correctness of the constructions on normal forms

-- The empty bag stands for the unit ε.

empty-correct : (ρ : Env n) → ⟦ empty ⟧⇓ ρ ≈ ε
empty-correct [] = refl
empty-correct (a ∷ ρ) = empty-correct ρ

-- The singleton bag stands for a single variable.

sg-correct : (x : Fin n) (ρ : Env n) →  ⟦ sg x ⟧⇓ ρ ≈ lookup ρ x
sg-correct zero (x ∷ ρ) = begin
    x ∙ ⟦ empty ⟧⇓ ρ   ≈⟨ ∙-congˡ (empty-correct ρ) ⟩
    x ∙ ε              ≈⟨ identityʳ _ ⟩
    x                  ∎
sg-correct (suc x) (m ∷ ρ) = sg-correct x ρ

-- Normal form composition corresponds to the composition of the monoid.

comp-correct : ∀ v w (ρ : Env n) →
               ⟦ v • w ⟧⇓ ρ ≈ (⟦ v ⟧⇓ ρ ∙ ⟦ w ⟧⇓ ρ)
comp-correct [] [] _ =  sym (identityˡ _)
comp-correct (l ∷ v) (m ∷ w) (a ∷ ρ) = lemma l m (comp-correct v w ρ)
  where
  lemma : ∀ l m {d b c} (p : d ≈ b ∙ c) →
          fold d (a ∙_) (l + m) ≈ fold b (a ∙_) l ∙ fold c (a ∙_) m
  lemma zero    zero    p = p
  lemma zero    (suc m) p = trans (∙-congˡ (lemma zero m p)) (x∙yz≈y∙xz _ _ _)
  lemma (suc l) m       p = trans (∙-congˡ (lemma l m p)) (sym (assoc a _ _))

------------------------------------------------------------------------
-- Normalization

-- A normaliser.

normalise : Expr n → Normal n
normalise (var x)   = sg x
normalise id        = empty
normalise (e₁ ⊕ e₂) = normalise e₁ • normalise e₂

-- The normaliser preserves the semantics of the expression.

correct : ∀ e ρ → ⟦ normalise {n = n} e ⟧⇓ ρ ≈ ⟦ e ⟧ ρ
correct (var x)   ρ = sg-correct x ρ
correct id        ρ = empty-correct ρ
correct (e₁ ⊕ e₂) ρ = begin
  ⟦ normalise e₁ • normalise e₂ ⟧⇓ ρ
    ≈⟨ comp-correct (normalise e₁) (normalise e₂) ρ ⟩
  ⟦ normalise e₁ ⟧⇓ ρ ∙ ⟦ normalise e₂ ⟧⇓ ρ
    ≈⟨ ∙-cong (correct e₁ ρ) (correct e₂ ρ) ⟩
  ⟦ e₁ ⟧ ρ ∙ ⟦ e₂ ⟧ ρ
    ∎
