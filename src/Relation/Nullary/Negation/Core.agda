------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties related to negation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Negation.Core where

open import Data.Empty using (⊥; ⊥-elim-irr)
open import Data.Sum.Base using (_⊎_; [_,_]; inj₁; inj₂)
open import Function.Base using (flip; _∘_; const)
open import Level

private
  variable
    a p q w : Level
    A B C : Set a
    Whatever : Set w

------------------------------------------------------------------------
-- Negation.

infix 3 ¬_
¬_ : Set a → Set a
¬ A = A → ⊥

------------------------------------------------------------------------
-- Stability.

-- Double-negation
DoubleNegation : Set a → Set a
DoubleNegation A = ¬ ¬ A

-- Stability under double-negation.
Stable : Set a → Set a
Stable A = ¬ ¬ A → A

------------------------------------------------------------------------
-- Relationship to sum

infixr 1 _¬-⊎_
_¬-⊎_ : ¬ A → ¬ B → ¬ (A ⊎ B)
_¬-⊎_ = [_,_]

------------------------------------------------------------------------
-- Uses of negation

contradiction-irr : .A → ¬ A → Whatever
contradiction-irr a ¬a = ⊥-elim-irr (¬a a)

contradiction : A → ¬ A → Whatever
contradiction a = contradiction-irr a

contradiction₂ : A ⊎ B → ¬ A → ¬ B → Whatever
contradiction₂ (inj₁ a) ¬a ¬b = contradiction a ¬a
contradiction₂ (inj₂ b) ¬a ¬b = contradiction b ¬b

contraposition : (A → B) → ¬ B → ¬ A
contraposition f ¬b a = contradiction (f a) ¬b

-- Everything is stable in the double-negation monad.
stable : ¬ ¬ Stable A
stable ¬[¬¬a→a] = ¬[¬¬a→a] (contradiction (¬[¬¬a→a] ∘ const))

-- Negated predicates are stable.
negated-stable : Stable (¬ A)
negated-stable ¬¬¬a a = ¬¬¬a (contradiction a)

¬¬-map : (A → B) → ¬ ¬ A → ¬ ¬ B
¬¬-map f = contraposition (contraposition f)

-- Note also the following use of flip:
private
  note : (A → ¬ B) → B → ¬ A
  note = flip

