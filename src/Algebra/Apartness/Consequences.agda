------------------------------------------------------------------------
-- The Agda standard library
--
-- Lemmas relating algebraic definitions wrt an apartness.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core using (Rel)

module Algebra.Apartness.Consequences
  {a ℓ} {A : Set a} (_#_ : Rel A ℓ) where

open import Algebra.Core using (Op₂)
open import Algebra.Apartness.Definitions _#_
open import Data.Product.Base using (_,_)
import Data.Sum.Base as Sum
open import Relation.Binary.Definitions
  using (Cotransitive)

private
  variable
    _∙_ : Op₂ A


------------------------------------------------------------------------
-- Cotransitive plus StronglyCongruent₂ implies StronglyExtensional

cotransitive∧congruent⇒extensional : Cotransitive _#_ →
  StronglyCongruent₂ _∙_ → StronglyExtensional _∙_
cotransitive∧congruent⇒extensional
  {_∙_ = _∙_} cotrans (congˡ , congʳ) {y = y} {w = w} xy#wz
  = Sum.map (congʳ y) (congˡ w) (cotrans xy#wz (w ∙ y))
