------------------------------------------------------------------------
-- The Agda standard library
--
-- An Equivalence (on functions) is an Equivalence relation
--   This file is meant to be imported qualified.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties.Equivalence where

open import Function.Bundles using (Equivalence; _⇔_)
open import Level using (Level)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (setoid)

import Function.Construct.Identity as Identity
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Composition as Composition

private
  variable
    a b ℓ₁ ℓ₂ : Level

------------------------------------------------------------------------
-- Setoid bundles

isEquivalence : IsEquivalence (Equivalence {a} {b})
isEquivalence = record
  { refl = λ {x} → Identity.equivalence x
  ; sym = Symmetry.equivalence
  ; trans = Composition.equivalence
  }

------------------------------------------------------------------------
-- Propositional bundles

⇔-isEquivalence : IsEquivalence {ℓ = ℓ₁} _⇔_
⇔-isEquivalence = record
  { refl = λ {x} → Identity.equivalence (setoid x)
  ; sym = Symmetry.equivalence
  ; trans = Composition.equivalence
  }
