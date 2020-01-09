------------------------------------------------------------------------
-- The Agda standard library
--
-- The basic code for equational reasoning with a single relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.Base.Single
  {a ℓ} {A : Set a} (_∼_ : Rel A ℓ)
  (refl : Reflexive _∼_) (trans : Transitive _∼_)
  where

------------------------------------------------------------------------
-- Reasoning combinators

-- Re-export combinators from partial reasoning

open import Relation.Binary.Reasoning.Base.Partial _∼_ trans public
  hiding (_∎⟨_⟩)

-- Redefine the terminating combinator now that we have reflexivity

infix  3 _∎

_∎ : ∀ x → x IsRelatedTo x
x ∎ = relTo refl
