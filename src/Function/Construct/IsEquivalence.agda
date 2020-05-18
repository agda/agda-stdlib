------------------------------------------------------------------------
-- The Agda standard library
--
-- Some functional properties are Equivalence Relations
--   This file is meant to be imported qualified.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Construct.IsEquivalence where

open import Data.Product using (_,_; swap)
open import Function
open import Level using (Level; _⊔_; suc)
open import Relation.Binary hiding (_⇔_)
open import Relation.Binary.PropositionalEquality using (setoid)

import Function.Construct.Identity as I
import Function.Construct.Symmetry as Sy
import Function.Construct.Composition as C

private
  variable
    a b ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Setoid bundles

module _ (R : Setoid a ℓ₁) (S : Setoid b ℓ₂) where

  inverse : IsEquivalence (Inverse {a} {b})
  inverse = record
    { refl = λ {x} → I.inverse x
    ; sym = Sy.inverse
    ; trans = C.inverse
    }

  equivalence : IsEquivalence (Equivalence {a} {b})
  equivalence = record
    { refl = λ {x} → I.equivalence x
    ; sym = Sy.equivalence
    ; trans = C.equivalence
    }

------------------------------------------------------------------------
-- Propositional bundles

-- need to η-expand for everything to line up properly
↔ : IsEquivalence {ℓ = ℓ₁} _↔_
↔ = record
  { refl = λ {x} → I.inverse (setoid x)
  ; sym = Sy.inverse
  ; trans = C.inverse
  }

⇔ : IsEquivalence {ℓ = ℓ₁} _⇔_
⇔ = record
  { refl = λ {x} → I.equivalence (setoid x)
  ; sym = Sy.equivalence
  ; trans = C.equivalence
  }
