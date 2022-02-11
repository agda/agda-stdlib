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
open import Relation.Binary.PropositionalEquality as P using (setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Function.Consequences

import Function.Construct.Identity as Identity
import Function.Construct.Symmetry as Symmetry
import Function.Construct.Composition as Composition

private
  variable
    a b ℓ ℓ₁ ℓ₂ : Level
    A B : Set a
    S T : Setoid a ℓ

------------------------------------------------------------------------
-- Setoid bundles

isEquivalence : IsEquivalence (Inverse {a} {b})
isEquivalence = record
  { refl  = λ {x} → Identity.inverse x
  ; sym   = Symmetry.inverse
  ; trans = Composition.inverse
  }

------------------------------------------------------------------------
-- Propositional bundles

-- need to η-expand for everything to line up properly
↔-isEquivalence : IsEquivalence {ℓ = ℓ} _↔_
↔-isEquivalence = record
  { refl  = λ {x} → Identity.inverse (P.setoid x)
  ; sym   = Symmetry.inverse
  ; trans = Composition.inverse
  }

------------------------------------------------------------------------
-- Conversion functions

Inverse⇒Injection : Inverse S T → Injection S T
Inverse⇒Injection {S = S} I = record
  { f = f
  ; cong = cong₁
  ; injective =  inverseʳ⇒injective S {f⁻¹ = f⁻¹} cong₂ inverseʳ
  } where open Inverse I

Inverse⇒Bijection : Inverse S T → Bijection S T
Inverse⇒Bijection {S = S} I = record
  { f         = f
  ; cong      = cong₁
  ; bijective = inverseᵇ⇒bijective S cong₂ inverse
  } where open Inverse I

Inverse⇒Equivalence : Inverse S T → Equivalence S T
Inverse⇒Equivalence I = record
  { f     = f
  ; g     = f⁻¹
  ; cong₁ = cong₁
  ; cong₂ = cong₂
  } where open Inverse I

↔⇒↣ : A ↔ B → A ↣ B
↔⇒↣ = Inverse⇒Injection

↔⇒⤖ : A ↔ B → A ⤖ B
↔⇒⤖ = Inverse⇒Bijection

↔⇒⇔ : A ↔ B → A ⇔ B
↔⇒⇔ = Inverse⇒Equivalence
