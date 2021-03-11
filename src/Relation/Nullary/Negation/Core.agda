------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties related to negation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Negation.Core where

open import Data.Bool.Base using (not)
open import Data.Empty
open import Data.Product
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (flip; _$_; _∘_; const)
open import Level
open import Relation.Nullary
open import Relation.Unary using (Pred)

private
  variable
    a p q w : Level
    A : Set a
    P : Set p
    Q : Set q
    Whatever : Set w

------------------------------------------------------------------------
-- Uses of negation

contradiction : P → ¬ P → Whatever
contradiction p ¬p = ⊥-elim (¬p p)

contradiction₂ : P ⊎ Q → ¬ P → ¬ Q → Whatever
contradiction₂ (inj₁ p) ¬p ¬q = contradiction p ¬p
contradiction₂ (inj₂ q) ¬p ¬q = contradiction q ¬q

contraposition : (P → Q) → ¬ Q → ¬ P
contraposition f ¬q p = contradiction (f p) ¬q

-- Note also the following use of flip:

private
  note : (P → ¬ Q) → Q → ¬ P
  note = flip

-- If we can decide P, then we can decide its negation.

¬-reflects : ∀ {b} → Reflects P b → Reflects (¬ P) (not b)
¬-reflects (ofʸ  p) = ofⁿ (_$ p)
¬-reflects (ofⁿ ¬p) = ofʸ ¬p

¬? : Dec P → Dec (¬ P)
does  (¬? p?) = not (does p?)
proof (¬? p?) = ¬-reflects (proof p?)

------------------------------------------------------------------------
-- Quantifier juggling

module _ {P : Pred A p} where

  ∃⟶¬∀¬ : ∃ P → ¬ (∀ x → ¬ P x)
  ∃⟶¬∀¬ = flip uncurry

  ∀⟶¬∃¬ : (∀ x → P x) → ¬ ∃ λ x → ¬ P x
  ∀⟶¬∃¬ ∀xPx (x , ¬Px) = ¬Px (∀xPx x)

  ¬∃⟶∀¬ : ¬ ∃ (λ x → P x) → ∀ x → ¬ P x
  ¬∃⟶∀¬ = curry

  ∀¬⟶¬∃ : (∀ x → ¬ P x) → ¬ ∃ (λ x → P x)
  ∀¬⟶¬∃ = uncurry

  ∃¬⟶¬∀ : ∃ (λ x → ¬ P x) → ¬ (∀ x → P x)
  ∃¬⟶¬∀ = flip ∀⟶¬∃¬

------------------------------------------------------------------------
-- Double-negation

¬¬-map : (P → Q) → ¬ ¬ P → ¬ ¬ Q
¬¬-map f = contraposition (contraposition f)

-- Stability under double-negation.

Stable : Set p → Set p
Stable P = ¬ ¬ P → P

-- Everything is stable in the double-negation monad.

stable : ¬ ¬ Stable P
stable ¬[¬¬p→p] = ¬[¬¬p→p] (λ ¬¬p → ⊥-elim (¬¬p (¬[¬¬p→p] ∘ const)))

-- Negated predicates are stable.

negated-stable : Stable (¬ P)
negated-stable ¬¬¬P P = ¬¬¬P (λ ¬P → ¬P P)
