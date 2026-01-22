------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for domain theory
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Domain.Bundles where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Structures using (IsDirectedFamily)
open import Relation.Binary.Domain.Structures
  using (IsDirectedCompletePartialOrder; IsScottContinuous
        ; IsLub)

private
  variable
    o ℓ e o' ℓ' e' ℓ₂ : Level
    Ix A B : Set o

------------------------------------------------------------------------
-- Directed Complete Partial Orders
------------------------------------------------------------------------

record DirectedFamily {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {B : Set c} : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    f : B → Poset.Carrier P
    isDirectedFamily : IsDirectedFamily (Poset._≈_ P) (Poset._≤_ P) f

  open IsDirectedFamily isDirectedFamily public

record DirectedCompletePartialOrder (c ℓ₁ ℓ₂ : Level) : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    poset                             : Poset c ℓ₁ ℓ₂
    isDirectedCompletePartialOrder    : IsDirectedCompletePartialOrder poset

  open Poset poset public
  open IsDirectedCompletePartialOrder isDirectedCompletePartialOrder public

------------------------------------------------------------------------
-- Scott-continuous functions
------------------------------------------------------------------------

record ScottContinuous
  {c₁ ℓ₁₁ ℓ₁₂ c₂ ℓ₂₁ ℓ₂₂ : Level}
  (P : Poset c₁ ℓ₁₁ ℓ₁₂)
  (Q : Poset c₂ ℓ₂₁ ℓ₂₂)
  (κ : Level) : Set (suc (κ ⊔ c₁ ⊔ ℓ₁₁ ⊔ ℓ₁₂ ⊔ c₂ ⊔ ℓ₂₁ ⊔ ℓ₂₂)) where
  field
    f                 : Poset.Carrier P → Poset.Carrier Q
    isScottContinuous : IsScottContinuous P Q f κ

  open IsScottContinuous isScottContinuous public

------------------------------------------------------------------------
-- Lubs
------------------------------------------------------------------------

record Lub {c ℓ₁ ℓ₂ : Level} {P : Poset c ℓ₁ ℓ₂} {B : Set c}
           (f : B → Poset.Carrier P) : Set (c ⊔ ℓ₁ ⊔ ℓ₂) where
  open Poset P
  field
    lub   : Carrier
    isLub : IsLub P f lub
