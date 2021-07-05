------------------------------------------------------------------------
-- The Agda standard library
--
-- Some functional properties are Equivalence Relations
--   This file is meant to be imported qualified.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Function.Properties.Inverse where

open import Data.Product using (_,_; proj₁; proj₂)
open import Function.Bundles
open import Level using (Level)
open import Relation.Binary using (Setoid; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Function.Consequences

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

------------------------------------------------------------------------
-- Conversion functions

module _ (A : Setoid a ℓ₁) (B : Setoid b ℓ₂) where

  Inverse⇒Bijection : Inverse A B → Bijection A B
  Inverse⇒Bijection record { f = f ; f⁻¹ = f⁻¹ ; cong₁ = cong₁ ; cong₂ = cong₂ ; inverse = inverse } = record
    { f         = f
    ; cong      = cong₁
    ; bijective = Inverseᵇ⇒Bijective A B cong₂ inverse }

  Inverse⇒Equivalence : Inverse A B → Equivalence A B
  Inverse⇒Equivalence record { f = f ; f⁻¹ = f⁻¹ ; cong₁ = cong₁ ; cong₂ = cong₂ } = record
    { f = f ; g = f⁻¹ ; cong₁ = cong₁ ; cong₂ = cong₂ }

module _ {A : Set a} {B : Set b} where

  ↔⇒⤖ : A ↔ B → A ⤖ B
  ↔⇒⤖ = Inverse⇒Bijection (setoid A) (setoid B)

  ↔⇒⇔ : A ↔ B → A ⇔ B
  ↔⇒⇔ = Inverse⇒Equivalence (setoid A) (setoid B)
