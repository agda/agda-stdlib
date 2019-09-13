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

open import Relation.Binary.Reasoning.Base.Partial _∼_ trans public

infix  3 _∎

_∎ : ∀ x → x IsRelatedTo x
x ∎ = x ∎⟨ refl ⟩
