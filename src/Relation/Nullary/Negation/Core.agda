------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties related to negation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Nullary.Negation.Core where

open import Data.Empty using (⊥; ⊥-elim-irr)
open import Data.Sum.Base using (_⊎_; [_,_]; inj₁; inj₂)
open import Function.Base using (_∘_; const)
open import Level using (Level; _⊔_)

private
  variable
    a w : Level
    A B C : Set a
    Whatever : Set w

------------------------------------------------------------------------
-- Definition.

infix 3 ¬_
¬_ : Set a → Set a
¬ A = A → ⊥

------------------------------------------------------------------------
-- Properties, I: as a definition in *minimal logic*

-- Contraposition
contraposition : (A → B) → ¬ B → ¬ A
contraposition f ¬b a =  ¬b (f a)

-- Relationship to sum
infixr 1 _¬-⊎_
_¬-⊎_ : ¬ A → ¬ B → ¬ (A ⊎ B)
_¬-⊎_ = [_,_]

-- Self-contradictory propositions are false by 'diagonalisation'
contra-diagonal : (A → ¬ A) → ¬ A
contra-diagonal self a = self a a

-- Double-negation
DoubleNegation : Set a → Set a
DoubleNegation A = ¬ ¬ A

-- Eta law for double-negation
¬¬-η : A → ¬ ¬ A
¬¬-η a ¬a = ¬a a

-- Functoriality for double-negation
¬¬-map : (A → B) → ¬ ¬ A → ¬ ¬ B
¬¬-map = contraposition ∘ contraposition

------------------------------------------------------------------------
-- Stability under double-negation.
Stable : Set a → Set a
Stable A = ¬ ¬ A → A

-- Negated predicates are stable.
negated-stable : Stable (¬ A)
negated-stable ¬¬¬a a = ¬¬¬a (¬¬-η a)

------------------------------------------------------------------------
-- Properties, II: using the *ex falso* rule ⊥-elim

contradiction : .A → .(¬ A) → Whatever
contradiction a ¬a = ⊥-elim-irr (¬a a)

contradiction′ : .(¬ A) → .A → Whatever
contradiction′ ¬a a = ⊥-elim-irr (¬a a)

contradiction₂ : A ⊎ B → ¬ A → ¬ B → Whatever
contradiction₂ (inj₁ a) ¬a ¬b = contradiction a ¬a
contradiction₂ (inj₂ b) ¬a ¬b = contradiction b ¬b

-- Everything is stable in the double-negation monad.
stable : ¬ ¬ Stable A
stable ¬[¬¬a→a] = ¬[¬¬a→a] λ ¬¬a → contradiction (¬[¬¬a→a] ∘ const) ¬¬a

