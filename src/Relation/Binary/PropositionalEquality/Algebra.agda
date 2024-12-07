------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional (intensional) equality - Algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.PropositionalEquality.Algebra where

open import Algebra.Bundles using (Magma)
open import Algebra.Core using (Op₂)
open import Algebra.Structures using (IsMagma)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong₂)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Any operation forms a magma over _≡_

isMagma : (_∙_ : Op₂ A) → IsMagma _≡_ _∙_
isMagma _∙_ = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _∙_
  }

magma : (_∙_ : Op₂ A) → Magma _ _
magma _∙_ = record
  { isMagma = isMagma _∙_
  }
