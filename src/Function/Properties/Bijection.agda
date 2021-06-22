------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of bijections. This file is designed to be
-- imported qualified.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties.Bijection where

open import Function.Bundles using (Bijection; _⤖_)
open import Level using (Level)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

import Function.Construct.Identity as Identity
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Composition as Composition

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A B : Set a
    T S : Setoid a ℓ

------------------------------------------------------------------------
-- Setoid properties

refl : Reflexive (Bijection {a} {ℓ})
refl = Identity.bijection _

-- Can't prove full symmetry as we have no proof that the witness
-- produced by the surjection proof preserves equality
sym-≡ : Bijection S (P.setoid B) → Bijection (P.setoid B) S
sym-≡ = Symmetry.bijection-≡

trans : Trans (Bijection {a} {ℓ₁} {b} {ℓ₂}) (Bijection {b} {ℓ₂} {c} {ℓ₃}) Bijection
trans = Composition.bijection

------------------------------------------------------------------------
-- Propositional properties

⤖-isEquivalence : IsEquivalence {ℓ = ℓ} _⤖_
⤖-isEquivalence = record
  { refl  = refl
  ; sym   = sym-≡
  ; trans = trans
  }
