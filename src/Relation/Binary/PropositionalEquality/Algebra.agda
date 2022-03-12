------------------------------------------------------------------------
-- The Agda standard library
--
-- Propositional (intensional) equality - Algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.PropositionalEquality.Algebra where

open import Algebra
open import Level
open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties

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
