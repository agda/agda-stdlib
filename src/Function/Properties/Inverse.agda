------------------------------------------------------------------------
-- The Agda standard library
--
-- Some functional properties are Equivalence Relations
--   This file is meant to be imported qualified.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties.Inverse where

open import Function.Bundles using (Inverse; _↔_)
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

isEquivalence : IsEquivalence (Inverse {a} {b})
isEquivalence = record
  { refl = λ {x} → Identity.inverse x
  ; sym = Symmetry.inverse
  ; trans = Composition.inverse
  }

------------------------------------------------------------------------
-- Propositional bundles

-- need to η-expand for everything to line up properly
↔-isEquivalence : IsEquivalence {ℓ = ℓ₁} _↔_
↔-isEquivalence = record
  { refl = λ {x} → Identity.inverse (setoid x)
  ; sym = Symmetry.inverse
  ; trans = Composition.inverse
  }
