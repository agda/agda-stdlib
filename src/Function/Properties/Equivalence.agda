------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of equivalences. This file is designed to be
-- imported qualified.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Properties.Equivalence where

open import Function.Bundles using (Equivalence; _⇔_)
open import Level
open import Relation.Binary using (Setoid; IsEquivalence)
import Relation.Binary.PropositionalEquality.Properties as Eq

import Function.Construct.Identity as Identity
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Composition as Composition

private
  variable
    a ℓ : Level

------------------------------------------------------------------------
-- Setoid bundles

isEquivalence : IsEquivalence (Equivalence {a} {ℓ})
isEquivalence = record
  { refl = λ {x} → Identity.equivalence x
  ; sym = Symmetry.equivalence
  ; trans = Composition.equivalence
  }

------------------------------------------------------------------------
-- Propositional bundles

⇔-isEquivalence : IsEquivalence {ℓ = ℓ} _⇔_
⇔-isEquivalence = record
  { refl = λ {x} → Identity.equivalence (Eq.setoid x)
  ; sym = Symmetry.equivalence
  ; trans = Composition.equivalence
  }


------------------------------------------------------------------------
-- Setoids

setoid : (s₁ s₂ : Level) → Setoid (suc (s₁ ⊔ s₂)) (s₁ ⊔ s₂)
setoid s₁ s₂ = record
  { Carrier       = Setoid s₁ s₂
  ; _≈_           = Equivalence
  ; isEquivalence = isEquivalence
  }

⇔-setoid : (ℓ : Level) → Setoid (suc ℓ) ℓ
⇔-setoid ℓ = record
  { Carrier       = Set ℓ
  ; _≈_           = _⇔_
  ; isEquivalence = ⇔-isEquivalence
  }
