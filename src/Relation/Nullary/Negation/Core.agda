------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties related to negation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Negation.Core where

open import Data.Bool.Base using (not)
open import Data.Empty using (⊥)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; [_,_]; inj₁; inj₂)
open import Function.Base using (flip; _$_; _∘_; const)
open import Level

private
  variable
    a p q w : Level
    A : Set a
    P : Set p
    Q : Set q
    Whatever : Set w

------------------------------------------------------------------------
-- Negation.

infix 3 ¬_
¬_ : Set a → Set a
¬ P = P → ⊥

-- Double-negation
DoubleNegation : Set p → Set p
DoubleNegation P = ¬ ¬ P

-- Stability under double-negation.
Stable : Set p → Set p
Stable P = ¬ ¬ P → P

------------------------------------------------------------------------
-- Relationship to product and sum

infixr 1 _¬-⊎_
_¬-⊎_ : ¬ P → ¬ Q → ¬ (P ⊎ Q)
_¬-⊎_ = [_,_]

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

-- Everything is stable in the double-negation monad.
stable : ¬ ¬ Stable P
stable ¬[¬¬p→p] = ¬[¬¬p→p] (λ ¬¬p → ⊥-elim (¬¬p (¬[¬¬p→p] ∘ const)))

-- Negated predicates are stable.
negated-stable : Stable (¬ P)
negated-stable ¬¬¬P P = ¬¬¬P (λ ¬P → ¬P P)

¬¬-map : (P → Q) → ¬ ¬ P → ¬ ¬ Q
¬¬-map f = contraposition (contraposition f)
